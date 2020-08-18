module RDL::Type
  class VarType < Type
    attr_reader :name, :cls, :meth, :category, :to_infer
    attr_accessor :lbounds, :ubounds, :solution

    @@cache = {}
    @@print_XXX = false

    class << self
      alias :__new__ :new
    end

    def self.new(name_or_hash)
      if name_or_hash.is_a?(Symbol) || name_or_hash.is_a?(String)
        name = name_or_hash.to_s.to_sym
        t = @@cache[name_or_hash]
        return t if t
        t = self.__new__ name
        return (@@cache[name_or_hash] = t) # assignment evaluates to t
      else
        # MILOD: I don't believe we want to cache these -- could result in clashes when we don't want them.
        #t = @@cache[name_or_hash]
        #return t if t

        t = self.__new__ name_or_hash

        #return (@@cache[name_or_hash] = t)
        return t
      end
    end

    def initialize(name_or_hash)
      if name_or_hash.is_a?(Symbol) || name_or_hash.is_a?(String)
        raise "weird" if name_or_hash.to_s == "expression"
        @name = name_or_hash
        @to_infer = false
      elsif name_or_hash.is_a?(Hash)
        @to_infer = true
        @lbounds = []
        @ubounds = []
        @solution = nil

        @cls = name_or_hash[:cls]
        @name = name_or_hash[:name] ## might be nil if category is :ret
        @meth = name_or_hash[:meth] ## might be nil if ccategory is :var
        @category = name_or_hash[:category]
      else
        raise "Unexpected argument #{name_or_hash} to RDL::Type::VarType.new."
      end
    end


    ## Adds an upper bound to self, and transitively pushes it to all of self's lower bounds.
    # [+ typ +] is the Type to add as upper bound.
    # [+ ast +] is the AST corresponding to the bound that is currently being propagated (for reporting errors).
    # [+ new_cons +] is a list of VarTypeBound elements. When provided, it can be used to roll back constraints
    # in case an error pops up. Each constraint comes with the list of constraints that lead to it
    # [+ causes + ] - list of VarTypeBound that led to this call
    def add_and_propagate_upper_bound(typ, ast, new_cons = [], causes = [])
      return if self.equal?(typ)
      RDL::Logging.log :typecheck, :trace,  "#{self} <= #{typ}"
      bound = add_ubound typ, ast, new_cons, causes, propagate: false

      if typ.is_a?(VarType) && !typ.lbounds
        RDL::Logging.debug_error :inference, "Nil found in lbounds... Returning"
        return
      end

      RDL::Logging.log :typecheck, :trace, 'lbounds.each'
      @lbounds.each { |lbound|

        lower_t = lbound.bound_type
        causes = [bound, lbound]
        RDL::Logging.log :typecheck, :trace, "lbound: #{lower_t}"

        if lower_t.is_a?(VarType) && lower_t.to_infer
          lower_t.add_and_propagate_upper_bound(typ, bound.asts, new_cons, causes) unless lower_t.ubounds.any? { |b| b.bound_type == typ }
        else
          if typ.is_a?(VarType) && !typ.lbounds.any? { |b| b.bound_type == lower_t }
            new_bound = VarTypeBound.new(typ, lower_t, :lower, bound.asts, causes)
            new_cons.append(new_bound)
          end

          RDL::Logging.log :typecheck, :trace, "about to check #{lower_t} <= #{typ} with".colorize(:green)
          RDL::Util.each_leq_constraints(new_cons) { |a, b| RDL::Logging.log(:typecheck, :trace, "#{a} <= #{b}") }

          unless RDL::Type::Type.leq(lower_t, typ, {}, false, ast: bound.asts, no_constraint: true, propagate: true, new_cons: new_cons, causes: causes)
            d1 = lbound.asts[0].nil? ? "" : (Diagnostic.new :note, :infer_constraint_error, [lower_t.to_s], lbound.asts[0].loc.expression).render.join("\n")
            d2 = bound.asts[0].nil? ? "" : (Diagnostic.new :note, :infer_constraint_error, [typ.to_s], bound.asts[0].loc.expression).render.join("\n")
            raise RDL::Typecheck::StaticTypeError.new(causes), ("Inconsistent type constraint #{lower_t} <= #{typ} generated during inference.\n #{d1}\n #{d2}")
          end
          RDL::Logging.log :typecheck, :trace, "Checked #{lower_t} <= #{typ}".colorize(:green)
        end
      }
    end

    ## Similar to above.
    def add_and_propagate_lower_bound(typ, ast, new_cons = [], causes = [])
      return if self.equal?(typ)
      RDL::Logging.log :typecheck, :trace,  "#{typ} <= #{self}"
      bound = add_lbound typ, ast, new_cons, causes, propagate: false

      if typ.is_a?(VarType) && !typ.ubounds
        RDL::Logging.debug_error :inference, "Nil found in ubounds... Returning"
        return
      end

      RDL::Logging.log :typecheck, :trace, 'ubounds.each'
      @ubounds.each { |ubound|

        upper_t = ubound.bound_type
        causes = [bound, ubound]
        RDL::Logging.log :typecheck, :trace, "ubound: #{upper_t}"

        if upper_t.is_a?(VarType) && upper_t.to_infer
          upper_t.add_and_propagate_lower_bound(typ, bound.asts, new_cons, causes) unless upper_t.lbounds.any? { |b| b.bound_type == typ }
        else
          if typ.is_a?(VarType) && !typ.ubounds.any? { |b| b.bound_type == upper_t }
            new_bound = VarTypeBound.new(typ, upper_t, :upper, bound.asts, causes)
            new_cons.append(new_bound)
          end

          RDL::Logging.log :typecheck, :trace, "about to check #{typ} <= #{upper_t} with".colorize(:green)
          RDL::Util.each_leq_constraints(new_cons) { |a, b| RDL::Logging.log(:typecheck, :trace, "#{a} <= #{b}") }

          unless RDL::Type::Type.leq(typ, upper_t, {}, false, ast: bound.asts, no_constraint: true, propagate: true, new_cons: new_cons, causes: causes)
            d1 = bound.asts[0].nil? ? "" : (Diagnostic.new :error, :infer_constraint_error, [typ.to_s], bound.asts[0].loc.expression).render.join("\n")
            d2 = ubound.asts[0].nil? ? "" : (Diagnostic.new :error, :infer_constraint_error, [upper_t.to_s], ubound.asts[0].loc.expression).render.join("\n")
            raise RDL::Typecheck::StaticTypeError.new(causes), ("Inconsistent type constraint #{typ} <= #{upper_t} generated during inference.\n #{d1}\n #{d2}")
          end
          RDL::Logging.log :typecheck, :trace, "Checked #{typ} <= #{upper_t}".colorize(:green)
        end
      }
    end

    def add_ubound(typ, ast, new_cons = [], causes = [], propagate: false)
      # raise "About to add upper bound #{self} <= #{typ}" if typ.is_a?(VarType) && !typ.to_infer
      return if self.equal?(typ)
      ast = [ast] unless ast.kind_of?(Array)  # since there can be several places in the AST that cause the same bound
      if !@ubounds.any? { |b| b.bound_type == typ}
        return add_and_propagate_upper_bound(typ, ast, new_cons, causes) if propagate
        bound = VarTypeBound.new(self, typ, :upper, ast, causes)
        new_cons.append(bound)
        @ubounds << bound
      else
        bound = @ubounds.select {|b| b.bound_type == typ}[0]
        bound.add_asts(ast) unless propagate
      end
      bound
    end

    def add_lbound(typ, ast, new_cons = [], causes = [], propagate: false)
      # raise "About to add lower bound #{typ} <= #{self}" if typ.is_a?(VarType) && !typ.to_infer
      # raise "ChoiceType!!!!" if typ.is_a? ChoiceType
      return if self.equal?(typ)
      ast = [ast] unless ast.kind_of?(Array)  # since there can be several places in the AST that cause the same bound
      RDL::Logging.log :typecheck, :trace, "#{self}.add_lbound(#{typ}); " + 'propagate'.colorize(:yellow) + " = #{propagate}"
      if !@lbounds.any? { |b| b.bound_type == typ}
        return add_and_propagate_lower_bound(typ, ast, new_cons, causes) if propagate
        bound = VarTypeBound.new(self, typ, :lower, ast, causes)
        new_cons.append(bound)
        @lbounds << bound
      else
        bound = @lbounds.select {|b| b.bound_type == typ}[0]
        bound.add_asts(ast) unless propagate
      end
      bound
    end

    def to_s # :nodoc:
      if @to_infer
        return 'XXX' if @@print_XXX

        "{ #{@cls}##{@meth} #{@category}: #{@name} }"
      else
        @name.to_s
      end
    end

    def base_name
      return nil unless @name
      ## if var represents returned value, then method name is closest thing we have to variable's name.
      if @category == :ret then @meth.to_s else @name.to_s.delete("@") end
    end

    def ==(other)
      return false if other.nil?
      other = other.canonical
      return (other.instance_of? self.class) && other.to_s == to_s#(other.name.to_s == @name.to_s)
    end

    alias eql? ==

    # an uninstantiated variable is only comparable to itself
    def <=(other)
      return Type.leq(self, other)
    end

    def match(other, type_var_table = {})
      other = other.canonical
      other = other.type if other.instance_of? AnnotatedArgType

      return true if other.instance_of? WildQuery
      return false unless other.instance_of? VarType

      name_sym = name.to_sym

      # If we've seen this type variable before, look up what it was originally
      # referencing and test that for equality with the current `other` type
      return type_var_table[name_sym] == other if type_var_table.key? name_sym

      # Otherwise, store the other type and return true.
      type_var_table[name_sym] = other
      true
    end

    def hash # :nodoc:
      return to_s.hash#@name.to_s.hash
    end

    def member?(obj, vars_wild: false)
      return true if vars_wild
      raise TypeError, "Unbound type variable #{@name}"
    end

    def instantiate(inst)
      return inst[@name] if inst[@name]
      return self
    end

    def widen
      return self
    end

    def copy
      self
    end

    def self.print_XXX!
      @@print_XXX = true
    end

    def self.no_print_XXX!
      @@print_XXX = false
    end

  end

  # A class to store information about a bound on a VarType.
  class VarTypeBound

    attr_reader :type  # The RDL::Type::VarType for which the bound is defined.
    attr_reader :bound_type  # The RDL::Type::Type by which @type is bounded.
    attr_reader :u_or_l  # The bound is either :upper or :lower.
    attr_reader :asts  # The list of asts from which the bound can be directly inferred (if any). Note that @asts is
    # a list and not a set because two identical Parser::AST::Nodes found at different locations hash to the same value.
    attr_reader :causes  # A list of bounds which, when propagated, generate this bound
    # (note that there might be many such lists)

    def initialize(type, bound_type, u_or_l, asts=[], causes=[])
      @type = type
      @bound_type = bound_type
      @u_or_l = u_or_l
      @asts = []
      @causes = causes
      add_asts asts
    end

    # Adds asts to the list of asts from which the bound can be inferred if
    # these asts is not already in the list
    # @param [Array<Parser::AST::Node>] asts to be added to the list
    def add_asts(asts)
      asts.map do
        |ast| @asts.append(ast) unless (ast == nil) || @asts.any? {|a| (a == ast) && (a.location == ast.location)}
      end
    end

    def ==(other)
      return false if other.nil?
      @u_or_l == other.u_or_l && @type == other.type && @bound_type == other.bound_type
    end

    def hash
      hashcode = @type.hash
      hashcode = hashcode * 31 + @bound_type.hash
      @u_or_l == :upper ? hashcode * 2 : hashcode # TODO - not sure that is the most effective approach
    end

    def to_s
      asts_as_string = asts.map {|ast|
        ast.nil? ? "" : (Diagnostic.new :note, :infer_constraint_error, [@bound_type.to_s], ast.loc.expression).render.join("\n")
      }.join("\n")
      bound_sign = u_or_l == :lower ? "<=" : ">="
      "%s %s %s, which comes from:\n%s" % [@type, bound_sign, @bound_type, asts_as_string]
    end

  end

end
