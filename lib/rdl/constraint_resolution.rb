require 'csv'
# require "z3"  # z3 API is broken and currently requires a fixed local copy

module RDL::Typecheck

  # Ranks RDL types by how likely they are to be the cause of an inconsistency:
  RANK = {RDL::Type::TupleType => 0, RDL::Type::VarType => 1,
          RDL::Type::SingletonType => 2, RDL::Type::FiniteHashType => 3,
          RDL::Type::UnionType => 4, RDL::Type::GenericType => 5,
          RDL::Type::StructuralType => 6, RDL::Type::NominalType => 7,
          RDL::Type::MethodType => 8, RDL::Type::BotType => 9,
          RDL::Type::OptionalType => 10, RDL::Type::TopType => 11,
          RDL::Type::ChoiceType => 12}


  # Propagate constraints. If there is a conflict, and
  # RDL::Config.instance.suggest_error_causes is true, come up with a set of
  # constrains that, when removed, cause the program to typecheck.
  def self.resolve_constraints
    solution = []  # constraints selected as faulty
    new_cores = attempt_to_resolve_constraints
    unsat_cores = new_cores
    until new_cores.empty?
      restore_constraints solution
      solution = get_minimal_unsat_core unsat_cores
      undo_constraints solution
      new_cores = attempt_to_resolve_constraints
      new_cores.map {|core| unsat_cores.append(core) unless unsat_cores.any? {
          |exist| (exist & core).length == exist.length}}
    end
    # report the obtained solution:
    unless solution.empty?
      error_string = solution.map {|bound| bound.to_s}.join("\n\n")
      error_string = "The constraints are unsatisfiable. Try removing the following constrains:\n%s" %(error_string)
      RDL::Logging.log :inference, :info, error_string
      unless RDL::Config.instance.continue_on_errors
        raise "Constraints unsatisfiable"
      end
    end
    return solution
  end


  # Propagate constraints. If there is a conflict, and
  # RDL::Config.instance.suggest_error_causes is on, return the unsat core the
  # list of all encountered unsat cores (one of which must have been causing
  # the conflict). Otherwise, raise an exception
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
          if (e.respond_to?(:causes)) && (e.causes != nil) && RDL::Config.instance.suggest_error_causes
            RDL::Logging.log :inference, :trace, "Found unsat core:\n" + (pp_unsat_core e.causes)
            cores = cores + [get_unsat_core(e.causes)]
          else
            raise e unless RDL::Config.instance.continue_on_errors
          end
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
  # @param [Array<VarTypeBound>] causes - list of inconsistent constraints
  # @return [Array<VarTypeBound>] - the unsat core, i.e. list of original
  #                                 constrains that cause the inconsistency
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

  # Return a string that contains all the information about an unsat core.
  # The string first lists the locations of all the generated constraints
  # contribution to an unsat core in a tree-like manner and then all the
  # constraints themselves
  def self.pp_unsat_core (causes)
    cause_dict = {}
    result = ""
    causes.each {|c| result = pp_unsat_core_recursive(c, "", cause_dict, result)}
    cause_dict.each_pair {|k, v| result += v.to_s + ")\t\n" + k}
    result
  end

  # A recursive helper function for pp_unsat_core
  def self.pp_unsat_core_recursive (bound, indent, dict, result)
    dict[bound.to_s_short] = dict.size unless dict.key? bound.to_s_short
    location = bound.asts.empty? ? "UNKNOWN" : bound.asts[0].location.expression.to_s
    result += indent + dict[bound.to_s_short].to_s + "\t"+ location + "\n"
    bound.causes.each do |c|
      result = pp_unsat_core_recursive c, indent + "\t", dict, result
    end
    result
  end

  # Get an array of unsat cores and use a greedy algorithm to produce a
  # set cover (logarithmic approximation)
  # @param [Array<Array<VarTypeBound>>] cores - an array of unsat cores, each of
  #                                             which is in itself an array of
  #                                             inconsistent constraints
  # @return [Array<VarTypeBound>] a potentially suboptimal set cover for
  #                               the cores (a list of constraints)
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


  # Get an array of unsat cores and use Z3 API and SMTs to produce a set cover
  # set cover (logarithmic approximation)
  # @param [Array<Array<VarTypeBound>>] cores - an array of unsat cores, each of
  #                                             which is in itself an array of
  #                                             inconsistent constraints
  # @return [Array<VarTypeBound>] a potentially suboptimal set cover for
  #                               the cores (a list of constraints)
  def self.get_minimal_unsat_core_z3 (cores)
    solver = Z3::Optimize.new
    RDL::Logging.log_header :inference, :info, "Looking for an optimal unsat core with z3"
    var_to_constraint = {}  # a hash from bool var to corresponding constraint
    constraint_to_var = {} # a hash in the reverse direction
    cores.each do |core|
      core_as_vars = []
      core.each do |bound|
        unless constraint_to_var.key? bound.to_s
          x = Z3.Bool bound.to_s
          var_to_constraint[x] = bound
          constraint_to_var[bound.to_s] = x
          solver.assert_soft !x, 1
        end
        core_as_vars.append constraint_to_var[bound.to_s]
      end
      solver.assert Z3.Or *core_as_vars
    end
    if solver.satisfiable? # must always be true
      return solver.model.select {|_, v| v.to_s == "true"}.map {|k, _| var_to_constraint[k]}
    end
  end

  # Greedily pick a constraint to be removed (a log. approximation of set cover)
  # @param [Array<Array<VarTypeBound>>] cores - an array of unsat cores, each of
  #                                             which is in itself an array of
  #                                             inconsistent constraints
  # @return [VarTypeBound] most commonly occurring constraint
  def self.pick_common_constraint(cores)
    cons = {}  # to calculate the # of cores a particular constraint appears in
    max = nil  # the constraint to be returned
    max_count = 0 # the number of cores max appears in
    max_type_rank = 0 # among equally frequent constraints,
    # pick one with highest RANK
    min_occ = -1 # among constraints with equal RANK,
    # pick one that can be inferred from as least AST nodes as possible
    cores.map do |core| core.map {|bound|
      cons[bound] = 1 + ((cons.key? bound) ? cons[bound] : 0)
      if (cons[bound] > max_count) ||
          ((cons[bound] == max_count) && (RANK[bound.bound_type.class] > max_type_rank)) ||
          ((cons[bound] == max_count) && (RANK[bound.bound_type.class] == max_type_rank) && (bound.asts.length < min_occ))
        max_count = cons[bound]
        max_type_rank = RANK[bound.bound_type.class]
        min_occ = bound.asts.length
        max = bound
      end
    } end
    max
  end

  # Display the decisions made by get_minimal_unsat_core as a string by
  # 1) assigning each constraint a unique identifier (number)
  # 2) representing each unsat core as a list of such identifiers
  # 3) representing the list of constraints chosen for removal by find_common_constraint as a list of identifiers
  #
  # @param [Array<Array<VarTypeBound>>] cores - a list of all unsat cores generated during the program run
  # @param [Array<Array<VarTypeBound>>] remaining - a list of remaining cores
  #                                                 (those that are yet to be covered by the solution)
  # @param [Array<VarTypeBound>] solution - a list of constraints that the program selected to try to ignore
  def self.display_progress (cores, remaining, solution, log=true)
    # first generate the unique indices for each constrain:
    inds = {}
    ind = 0
    constraint_string = []
    cores.map { |core| core.map {|bound|
      inds[bound] = ind if !inds.key? bound
      constraint_string << bound.to_s
      ind += 1
    }}
    constraint_string = constraint_string.join("\n")
    # represent each core as a list of identifiers:
    cores_string = remaining.map { |core| core.map {|bound| inds[bound].to_s }.
        join("\t") }.join("\n")
    # represent the solution as a list of identfiers:
    solution_string = solution.map { |bound| inds[bound].to_s}.join("\t")
    RDL::Logging.log :inference, :debug,
                     "Cores unaccounted for:\n%s\nConstraints in the solution:"\
                     " %s" %[cores_string, solution_string] if log
    [cores_string, solution_string, constraint_string]
  end


  # Use the solutions generated during constraint extraction to output in the
  # log the possible typecasts that could be added to remove the constraints
  # previously found faulty during constraint_resolution
  def self.generate_typecasts(constraints)
    debug_string = constraints.map {|bound|
      RDL::Type::VarType.print_XXX!
      if bound.u_or_l == :upper
        lower_str = bound.type.solution.to_s
        upper_str = bound.bound_type.solution ?
                        bound.bound_type.solution.to_s : bound.bound_type.to_s
      else
        upper_str = bound.type.solution.to_s
        lower_str = bound.bound_type.solution ?
                        bound.bound_type.solution.to_s : bound.bound_type.to_s
      end
      RDL::Type::VarType.no_print_XXX!
      type_cast_string = "Try typecasting the lower bound to %s or the upper bound to %s." % ([lower_str, upper_str])
      bound.to_s  + "\n" + type_cast_string
    }.join("\n\n")
    RDL::Logging.log :inference, :info, debug_string
  end

end
