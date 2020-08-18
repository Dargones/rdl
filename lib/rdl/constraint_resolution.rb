require 'csv'

module RDL::Typecheck

  # Propagate constraints. If there is a conflict, and RDL::Config.instance.suggest_error_causes is on, come up with
  # a set constrains that, when removed, cause the program to typecheck and remove the said constrains.
  def self.resolve_constraints
    solution = []  # constraints to ignore during resolution (i.e. potentially faulty constraints)
    new_cores = attempt_to_resolve_constraints
    unsat_cores = new_cores
    until new_cores.empty?
      restore_constraints solution
      solution = get_minimal_unsat_core unsat_cores
      undo_constraints solution
      new_cores = attempt_to_resolve_constraints
      new_cores.map {|core| unsat_cores.append(core) unless unsat_cores.any? {|exist| (exist & core).length == exist.length}}
    end
    unless solution.empty? || RDL::Config.instance.continue_on_errors
      error_string = solution.map {|bound| bound.to_s}.join("\n\n")
      raise "The constraints are unsatisfiable. Try removing the following constrains:\n%s" %(error_string) unless RDL::Config.instance.continue_on_errors
    end
  end

  # Propagate constraints. If there is a conflict, and RDL::Config.instance.suggest_error_causes is on, return the unsat
  # core that caused the conflict. Otherwise, if RDL::Config.continue_on_errors is on, return an empty list. Otherwise,
  # raise an exception
  def self.attempt_to_resolve_constraints
    cores = []
    new_cons = []
    RDL::Logging.log_header :inference, :info, "Starting constraint resolution..."
    RDL::Globals.constrained_types.each { |klass, name|
      RDL::Logging.log :inference, :debug, "Resolving constraints from #{RDL::Util.pp_klass_method(klass, name)}"
      typ = RDL::Globals.info.get(klass, name, :type)
      ## If typ is an Array, then it's an array of method types
      ## but for inference, we only use a single method type.
      ## Otherwise, it's a single VarType for an instance/class var.
      if typ.is_a?(Array)
        var_types = name == :initialize ? typ[0].args + [typ[0].block] : typ[0].args + [typ[0].block, typ[0].ret]
      else
        var_types = [typ]
      end

      var_types.each { |var_type|
        begin
          if var_type.var_type? || var_type.optional_var_type? || var_type.vararg_var_type?
            var_type = var_type.type if var_type.optional_var_type? || var_type.vararg_var_type?
            var_type.lbounds.each { |bound|
              RDL::Logging.log :typecheck, :trace, "#{bound.bound_type} <= #{var_type}"
              var_type.add_and_propagate_lower_bound(bound.bound_type, [], new_cons)
            }
            var_type.ubounds.each { |bound|
              var_type.add_and_propagate_upper_bound(bound.bound_type, [], new_cons)
            }
          elsif var_type.fht_var_type?
            var_type.elts.values.each { |v|
              vt = v.optional_var_type? || v.vararg_var_type? ? v.type : v
              vt.lbounds.each { |bound|
                vt.add_and_propagate_lower_bound(bound.bound_type, [], new_cons)
              }
              vt.ubounds.each { |bound|
                vt.add_and_propagate_upper_bound(bound.bound_type, [], new_cons)
              }
            }
          else
            raise "Got unexpected type #{var_type}."
          end
        rescue => e
          RDL::Logging.log :inference, :debug_error, "Caught error when resolving constraints for #{var_type}; skipping..."
          raise e unless RDL::Config.instance.continue_on_errors || ((e.respond_to?(:causes)) && (e.causes != nil) && RDL::Config.instance.suggest_error_causes)
          cores = cores + [get_unsat_core(e.causes)] if RDL::Config.instance.suggest_error_causes
        end
      }
    }
    unless cores.empty?
      undo_constraints new_cons
    end
    return cores
  end

  # Remove the given set of constraints
  # @param [Array<VarTypeBound>] cons - a list of constraint to be removed
  def self.undo_constraints(cons)
    cons.each do |bound|
      if bound.u_or_l == :upper
        bound.type.ubounds.reject! {|b| b == bound}
      else
        bound.type.lbounds.reject! {|b| b == bound}
      end
    end
  end

  # Reverse the effect of undo_constraints
  # @param [Array<VarTypeBound>] cons - a list of constraint to be added back
  def self.restore_constraints(cons)
    cons.each do |bound|
      if bound.u_or_l == :upper
        bound.type.ubounds << bound
      else
        bound.type.lbounds << bound
      end
    end
  end

  # Generate the unsat core given the set of constraints that are inconsistent
  # @param [Array<VarTypeBound>] causes - list of constrains(bounds) that are inconsistent
  # @return [Array<VarTypeBound>] - the unsat core, i.e. list of original constrains that bring about the inconsistency
  def self.get_unsat_core (causes)
    core = []
    until causes.empty?
      bound = causes.pop
      if bound.causes.empty?
        core = core | [bound]
      else
        causes = causes | bound.causes
      end
    end
    return core
  end

  # Get an array of unsat cores and use a greedy algorithm to produce a set cover (logarithmic approximation)
  # @param [Array<Array<VarTypeBound>>] cores - is a an array of unsat cores, each of which is in itself an array of
  # constraints that are inconsistent
  # @return [Array<VarTypeBound>] a potentially suboptimal set cover for the cores (a list of constraints)
  def self.get_minimal_unsat_core (cores)
    RDL::Logging.log_header :inference, :info, "Looking for an optimal unsat core"
    solution = []
    cores_remaining = cores  # cores that are yet to be covered by the solution
    until cores_remaining.empty?
      solution.append(pick_common_constraint(cores_remaining))
      display_progress cores, cores_remaining, solution
      cores_remaining = cores_remaining.select {|core| (core & solution).empty?}
    end
    solution
  end

  # Greedily pick a constraint to be removed (a logarithmic approximation of set cover)
  # @param [Array<Array<VarTypeBound>>] cores - is a an array of unsat cores, each of which is in itself an array of
  # constraints that are inconsistent
  # @return [VarTypeBound] a single constrain that appears in a maximum number of cores.
  def self.pick_common_constraint(cores)
    cons = {}  # a dictionary to calculate the number of cores a particular constraint appears in
    max = nil  # the constraint to be returned
    max_count = 0 # the number of cores max appears in
    # min_occ = -1  # comment out
    cores.map do |core| core.map {|bound|
      cons[bound] = 1 + ((cons.key? bound) ? cons[bound] : 0)
      if cons[bound] > max_count
        # if (cons[bound] > max_count) || ((cons[bound] == max_count) && (bound.asts.length < min_occ))  # comment out
        max_count = cons[bound]
        # min_occ = bound.asts.length  # comment out
        max = bound
      end
    } end
    max
  end

  # Display the decisions made by find_common_constraint and get_minimal_unsat_core as a string by
  # 1) assigning each constraint a unique identifier (number)
  # 2) representing each unsat core as a list of such identifiers
  # 3) representing the list of constraints chosen for removal by find_common_constraint as a list of identifiers
  #
  # @param [Array<Array<VarTypeBound>>] cores - a list of all unsat cores generated during the program run
  # @param [Array<Array<VarTypeBound>>] remaining - a list of remaining cores
  #                                                 (those that are yet to be covered by the solution)
  # @param [Array<VarTypeBound>] solution - a list of constraints that the program selected to try to ignore
  def self.display_progress (cores, remaining, solution)
    # first generate the unique indices for each constrain:
    inds = {}
    ind = 0
    cores.map { |core| core.map {|bound|
      inds[bound] = ind if !inds.key? bound
      ind += 1
    }}
    # represent each core as a list of identifiers:
    cores_string = remaining.map { |core| core.map {|bound| inds[bound].to_s }.join("\t") }.join("\n")
    # represent the solution as a list of identfiers:
    solution_string = solution.map { |bound| inds[bound].to_s}.join("\t")
    RDL::Logging.log :inference, :info,
                     "Cores unaccounted for:\n%s\nConstraints in the solution: %s" %[cores_string, solution_string]
  end

end
