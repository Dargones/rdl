module RDL::Typecheck

  def self.resolve_constraints
    puts "Starting constraint resolution..."
    RDL::Globals.constrained_types.each { |klass, name|
      puts "Resolving constraints from #{klass} and #{name}"
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
        if var_type.var_type? || var_type.optional_var_type?        
          var_type = var_type.type if var_type.is_a?(RDL::Type::OptionalType)
          var_type.lbounds.each { |lower_t, ast|
            #puts "1. Gonna apply #{lower_t} <= #{var_type}"
            var_type.add_and_propagate_lower_bound(lower_t, ast)
          }
          var_type.ubounds.each { |upper_t, ast|
            #puts "2. Gonna apply #{var_type} <= #{upper_t}"
            var_type.add_and_propagate_upper_bound(upper_t, ast)
          }
        elsif var_type.fht_var_type?
          var_type.elts.values.each { |v|
            vt = v.is_a?(RDL::Type::OptionalType) ? v.type : v
            vt.lbounds.each { |lower_t, ast|
              vt.add_and_propagate_lower_bound(lower_t, ast)
            }
            vt.ubounds.each { |upper_t, ast|
              vt.add_and_propagate_upper_bound(upper_t, ast)
            }            
          }
        else
          raise "Got unexpected type #{var_type}."
        end
      }
    }
  end

  def self.extract_var_sol(var, category)
    #raise "Expected VarType, got #{var}." unless var.is_a?(RDL::Type::VarType)
    return var.canonical unless var.is_a?(RDL::Type::VarType)
    if category == :arg
      non_vartype_ubounds = var.ubounds.map { |t, ast| t}.reject { |t| t.is_a?(RDL::Type::VarType) }
      sol = non_vartype_ubounds.size == 1 ? non_vartype_ubounds[0] : RDL::Type::IntersectionType.new(*non_vartype_ubounds).canonical
      #return sol
    elsif category == :ret
      non_vartype_lbounds = var.lbounds.map { |t, ast| t}.reject { |t| t.is_a?(RDL::Type::VarType) }
      sol = RDL::Type::UnionType.new(*non_vartype_lbounds)
      sol = sol.drop_vars!.canonical if sol.is_a?(RDL::Type::UnionType) && !sol.types.all? { |t| t.is_a?(RDL::Type::VarType) } ## could be, e.g., nominal type if only one type used to create union.
      #return sol
    elsif category == :var
      if var.lbounds.empty? || (var.lbounds.size == 1 && var.lbounds[0][0] == RDL::Globals.types[:bot])
        ## use upper bounds in this case.
        non_vartype_ubounds = var.ubounds.map { |t, ast| t}.reject { |t| t.is_a?(RDL::Type::VarType) }
        sol = RDL::Type::IntersectionType.new(*non_vartype_ubounds).canonical
        #return sol
      else
        ## use lower bounds
        non_vartype_lbounds = var.lbounds.map { |t, ast| t}.reject { |t| t.is_a?(RDL::Type::VarType) }
        sol = RDL::Type::UnionType.new(*non_vartype_lbounds)
        sol = sol.drop_vars!.canonical if sol.is_a?(RDL::Type::UnionType) && !sol.types.all? { |t| t.is_a?(RDL::Type::VarType) } ## could be, e.g., nominal type if only one type used to create union.
        #return sol#RDL::Type::UnionType.new(*non_vartype_lbounds).canonical
      end
    else
      raise "Unexpected VarType category #{category}."
    end
    if sol.is_a?(RDL::Type::UnionType) || (sol == RDL::Globals.types[:bot]) || sol.is_a?(RDL::Type::StructuralType) || sol.is_a?(RDL::Type::IntersectionType) || (sol == RDL::Globals.types[:object]) 
      ## Try each rule. Return first non-nil result.
      ## If no non-nil results, return original solution.
      ## TODO: check constraints.

      RDL::Heuristic.rules.each { |name, rule|
        #puts "Trying rule `#{name}` for variable #{var}."
        typ = rule.call(var)
        new_cons = {}
        begin
          if typ
            typ = typ.canonical
            var.add_and_propagate_upper_bound(typ, nil, new_cons)
            var.add_and_propagate_lower_bound(typ, nil, new_cons)
            @new_constraints = true if !new_cons.empty?
            return typ
            #sol = typ
          end
        rescue RDL::Typecheck::StaticTypeError => e
          puts "Attempted to apply rule #{name} to var #{var}, but go the following error: "
          puts e
          undo_constraints(new_cons)
          ## no new constraints in this case so we'll leave it as is
        end
      }

    end
    ## out here, none of the heuristics applied.
    ## Try to use `sol` as solution -- there is a chance it will 
    begin
      new_cons = {}
      sol = var if sol == RDL::Globals.types[:bot] # just use var itself when result of solution extraction was %bot.
      sol = sol.canonical
      var.add_and_propagate_upper_bound(sol, nil, new_cons)
      var.add_and_propagate_lower_bound(sol, nil, new_cons)
      @new_constraints = true if !new_cons.empty?
    rescue RDL::Typecheck::StaticTypeError => e
      puts "Attempted to apply solution #{sol} for var #{var} but got the following error: "
      puts e
      undo_constraints(new_cons)
      ## no new constraints in this case so we'll leave it as is
      ### MILOD TODO TOMORROW: set sol = the original var here.
    end

    return sol
  end

  # [+ cons +] is Hash<VarType, [:upper or :lower], Type, AST> of constraints to be undone.
  def self.undo_constraints(cons)
    cons.each_key { |var_type|
      cons[var_type].each { |upper_or_lower, bound_t, ast|
        if upper_or_lower == :upper
          var_type.ubounds.delete([bound_t, ast])
        elsif upper_or_lower == :lower
          var_type.lbounds.delete([bound_t, ast])
        end
      }
    }
  end

  def self.extract_meth_sol(tmeth)
    raise "Expected MethodType, got #{tmeth}." unless tmeth.is_a?(RDL::Type::MethodType)
    ## ARG SOLUTIONS
    arg_sols = tmeth.args.map { |a|
      if a.optional_var_type?
        RDL::Type::OptionalType.new(extract_var_sol(a.type, :arg))
      elsif a.fht_var_type?
        hash_sol = a.elts.transform_values { |v|
          if v.is_a?(RDL::Type::OptionalType)
            RDL::Type::OptionalType.new(extract_var_sol(v.type, :arg))
          else
            extract_var_sol(v, :arg)
          end
        }
        RDL::Type::FiniteHashType.new(hash_sol, nil)
      else
        extract_var_sol(a, :arg)
      end
    }

    ## BLOCK SOLUTION
    if tmeth.block && !tmeth.block.ubounds.empty?
      non_vartype_ubounds = tmeth.block.ubounds.map { |t, ast| t.canonical }.reject { |t| t.is_a?(RDL::Type::VarType) }          
      block_sol = non_vartype_ubounds.size > 1 ? RDL::Type::IntersectionType.new(*non_vartype_ubounds).canonical : non_vartype_bounds[0] ## doing this once and calling canonical to remove any supertypes that would be eliminated anyway
      block_sols = []
      block_sol.types.each { |m|
        raise "Expected block type to be a MethodType, got #{m}." unless m.is_a?(RDL::Type::MethodType)
        block_sols << RDL::Type::MethodType.new(*extract_meth_sol(m))
      }
      block_sol = RDL::Type::IntersectionType.new(*block_sols).canonical
    else
      block_sol = nil
    end

    ## RET SOLUTION
    ret_sol = tmeth.ret.is_a?(RDL::Type::VarType) ?  extract_var_sol(tmeth.ret, :ret) : tmeth.ret

    return [arg_sols, block_sol, ret_sol]
  end
  
  def self.extract_solutions
    ## Go through once to come up with solution for all var types.
    #until !@new_constraints
    loop do
      @new_constraints = false
      puts "\n\nRunning solution extraction..."
      RDL::Globals.constrained_types.each { |klass, name|
        typ = RDL::Globals.info.get(klass, name, :type)
        if typ.is_a?(Array)
          raise "Expected just one method type for #{klass}#{name}." unless typ.size == 1
          tmeth = typ[0]

          arg_sols, block_sol, ret_sol = extract_meth_sol(tmeth)

          block_string = block_sol ? " { #{block_sol} }" : nil
          puts "Extracted solution for #{klass}\##{name} is (#{arg_sols.join(',')})#{block_string} -> #{ret_sol}"

        elsif name.to_s == "splat_param"
        else
          ## Instance/Class (also some times splat parameter) variables:
          ## There is no clear answer as to what to do in this case.
          ## Just need to pick something in between bounds (inclusive).
          ## For now, plan is to just use lower bound when it's not empty/%bot,
          ## otherwise use upper bound.
          ## Can improve later if desired.
          var_sol = extract_var_sol(typ, :var)
          #typ.solution = var_sol
          
          puts "Extracted solution for #{typ} is #{var_sol}."
        end
      }
      break if !@new_constraints
    end
  end
end