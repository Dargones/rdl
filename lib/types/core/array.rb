RDL.nowrap :Array

RDL.type_params :Array, [:t], :all?

RDL.type :Array, :<<, '(t) -> Array<t>'
RDL.type :Array, :[], '(Range<Integer>) -> Array<t>'
#RDL.type :Array, :[], '(Integer or Float) -> t'
RDL.type :Array, :[], '(Integer or Float) -> ``access_output(trec, targs)``'

def Array.access_output(trec, targs)
  case trec
  when RDL::Type::TupleType
    case targs[0]
    when RDL::Type::SingletonType
      return trec.params[targs[0].val]
    else
      return trec.promote.params[0]
    end
  else
    vartype_name = RDL::Globals.type_params["Array"][0][0]
    RDL::Type::VarType.new(vartype_name)
  end
end

RDL.type :Array, :[], '(Integer, Integer) -> Array<t>'
RDL.type :Array, :&, '(Array<u>) -> Array<t>'
RDL.type :Array, :*, '(Integer) -> Array<t>'
RDL.type :Array, :*, '(String) -> String'
RDL.type :Array, :+, '(Enumerable<u>) -> Array<u or t>'
#RDL.type :Array, :+, '(Array<u>) -> Array<u or t>'
RDL.type :Array, :+, '(``plus_input(targs)``) -> ``plus_output(trec, targs)``'
def Array.plus_input(targs)
  case targs[0]
  when RDL::Type::TupleType
    return targs[0]
  when RDL::Type::GenericType
    return RDL::Globals.parser.scan_str "#T Array<u>"
  else
    RDL::Globals.types[:array]
  end
end

def Array.plus_output(trec, targs)
  case trec
  when RDL::Type::NominalType
    return RDL::Globals.types[:array]
  when RDL::Type::GenericType
    case targs[0]
    when RDL::Type::TupleType
      promoted = targs[0].promote
      param_union = RDL::Type::UnionType.new(promoted.params[0], trec.params[0])
      return RDL::Type::GenericType.new(trec.base, param_union)
    when RDL::Type::GenericType
      return RDL::Globals.parser.scan_str "#T Array<u or t>"
    else
      ## targs[0] should just be array here
      return RDL::Globals.types[:array]
    end
  when RDL::Type::TupleType
    case targs[0]
    when RDL::Type::TupleType
      return RDL::Type::TupleType.new(*(trec.params + targs[0].params))
    when RDL::Type::GenericType
      promoted = trec.promote
      param_union = RDL::Type::UnionType.new(promoted.params[0], targs[0].params[0])
      return RDL::Type::GenericType.new(targs[0].base, param_union)
    else
      ## targs[0] should just be Array here
      return RDL::Globals.types[:array]
    end
  end
end






RDL.type :Array, :-, '(Array<u>) -> Array<u or t>'
RDL.type :Array, :slice, '(Range<Integer>) -> Array<t>'
RDL.type :Array, :slice, '(Integer) -> t'
RDL.type :Array, :slice, '(Integer, Integer) -> Array<t>'
RDL.type :Array, :[]=, '(Integer, t) -> t'
RDL.type :Array, :[]=, '(Integer, Integer, t) -> t'
# RDL.type :Array, :[]=, '(Integer, Integer, Array<t>) -> Array<t>'
# RDL.type :Array, :[]=, '(Range, Array<t>) -> Array<t>'
RDL.type :Array, :[]=, '(Range<Integer>, t) -> t'
RDL.type :Array, :assoc, '(t) -> Array<t>'
RDL.type :Array, :at, '(Integer) -> t'
RDL.type :Array, :clear, '() -> Array<t>'
RDL.type :Array, :map, '() {(t) -> u} -> Array<u>'
RDL.type :Array, :map, '() -> Enumerator<t>'
RDL.type :Array, :map!, '() {(t) -> u} -> Array<u>'
RDL.type :Array, :map!, '() -> Enumerator<t>'
RDL.type :Array, :collect, '() { (t) -> u } -> Array<u>'
RDL.type :Array, :collect, '() -> Enumerator<t>'
RDL.type :Array, :combination, '(Integer) { (Array<t>) -> %any } -> Array<t>'
RDL.type :Array, :combination, '(Integer) -> Enumerator<t>'
RDL.type :Array, :push, '(*t) -> Array<t>'
RDL.type :Array, :compact, '() -> Array<t>'
RDL.type :Array, :compact!, '() -> Array<t>'
RDL.type :Array, :concat, '(Array<t>) -> Array<t>'
RDL.type :Array, :count, '() -> Integer'
RDL.type :Array, :count, '(t) -> Integer'
RDL.type :Array, :count, '() { (t) -> %bool } -> Integer'
RDL.type :Array, :cycle, '(?Integer) { (t) -> %any } -> %any'
RDL.type :Array, :cycle, '(?Integer) -> Enumerator<t>'
RDL.type :Array, :delete, '(u) -> t'
RDL.type :Array, :delete, '(u) { () -> v } -> t or v'
RDL.type :Array, :delete_at, '(Integer) -> Array<t>'
RDL.type :Array, :delete_if, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :delete_if, '() -> Enumerator<t>'
RDL.type :Array, :drop, '(Integer) -> Array<t>'
RDL.type :Array, :drop_while, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :drop_while, '() -> Enumerator<t>'
RDL.type :Array, :each, '() -> Enumerator<t>'
RDL.type :Array, :each, '() { (t) -> %any } -> Array<t>'
RDL.type :Array, :each_index, '() { (Integer) -> %any } -> Array<t>'
RDL.type :Array, :each_index, '() -> Enumerator<t>'
RDL.type :Array, :empty?, '() -> %bool'
RDL.type :Array, :fetch, '(Integer) -> t'
RDL.type :Array, :fetch, '(Integer, u) -> u'
RDL.type :Array, :fetch, '(Integer) { (Integer) -> u } -> t or u'
RDL.type :Array, :fill, '(t) -> Array<t>'
RDL.type :Array, :fill, '(t, Integer, ?Integer) -> Array<t>'
RDL.type :Array, :fill, '(t, Range<Integer>) -> Array<t>'
RDL.type :Array, :fill, '() { (Integer) -> t } -> Array<t>'
RDL.type :Array, :fill, '(Integer, ?Integer) { (Integer) -> t } -> Array<t>'
RDL.type :Array, :fill, '(Range<Integer>) { (Integer) -> t } -> Array<t>'
RDL.type :Array, :flatten, '() -> Array<%any>' # Can't give a more precise RDL.type
RDL.type :Array, :index, '(u) -> Integer'
RDL.type :Array, :index, '() { (t) -> %bool } -> Integer'
RDL.type :Array, :index, '() -> Enumerator<t>'
RDL.type :Array, :first, '() -> t'
RDL.type :Array, :first, '(Integer) -> Array<t>'

#RDL.type :Array, :include?, '(u) -> %bool'
RDL.type :Array, :include?, '(%any) -> ``include_output(trec, targs)``'

def Array.include_output(trec, targs)
  case trec
  when RDL::Type::TupleType
    case targs[0]
    when RDL::Type::SingletonType
      if trec.params.include?(targs[0])
        RDL::Globals.types[:true]
      else
        ## in this case, still can't say false because arg may be in tuple, but without singleton type.
        RDL::Globals.types[:bool]
      end
    else
      RDL::Globals.types[:bool]
    end
  else
    RDL::Globals.types[:bool]
  end
end





RDL.type :Array, :initialize, '() -> self'
RDL.type :Array, :initialize, '(Integer) -> self'
RDL.type :Array, :initialize, '(Integer, t) -> self<t>'
RDL.type :Array, :insert, '(Integer, *t) -> Array<t>'
RDL.type :Array, :inspect, '() -> String'
RDL.type :Array, :join, '(?String) -> String'
RDL.type :Array, :keep_if, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :last, '() -> t'
RDL.type :Array, :last, '(Integer) -> Array<t>'
RDL.type :Array, :member, '(u) -> %bool'
RDL.type :Array, :length, '() -> Integer'
RDL.type :Array, :permutation, '(?Integer) -> Enumerator<t>'
RDL.type :Array, :permutation, '(?Integer) { (Array<t>) -> %any } -> Array<t>'
RDL.type :Array, :pop, '(Integer) -> Array<t>'
RDL.type :Array, :pop, '() -> t'
RDL.type :Array, :product, '(*Array<u>) -> Array<Array<t or u>>'
RDL.type :Array, :rassoc, '(u) -> t'
RDL.type :Array, :reject, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :reject, '() -> Enumerator<t>'
RDL.type :Array, :reject!, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :reject!, '() -> Enumerator<t>'
RDL.type :Array, :repeated_combination, '(Integer) { (Array<t>) -> %any } -> Array<t>'
RDL.type :Array, :repeated_combination, '(Integer) -> Enumerator<t>'
RDL.type :Array, :repeated_permutation, '(Integer) { (Array<t>) -> %any } -> Array<t>'
RDL.type :Array, :repeated_permutation, '(Integer) -> Enumerator<t>'
RDL.type :Array, :reverse, '() -> Array<t>'
RDL.type :Array, :reverse!, '() -> Array<t>'
RDL.type :Array, :reverse_each, '() { (t) -> %any } -> Array<t>'
RDL.type :Array, :reverse_each, '() -> Enumerator<t>'
RDL.type :Array, :rindex, '(u) -> t'
RDL.type :Array, :rindex, '() { (t) -> %bool } -> Integer'
RDL.type :Array, :rindex, '() -> Enumerator<t>'
RDL.type :Array, :rotate, '(?Integer) -> Array<t>'
RDL.type :Array, :rotate!, '(?Integer) -> Array<t>'
RDL.type :Array, :sample, '() -> t'
RDL.type :Array, :sample, '(Integer) -> Array<t>'
RDL.type :Array, :select, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :select, '() -> Enumerator<t>'
RDL.type :Array, :select!, '() { (t) -> %bool } -> Array<t>'
RDL.type :Array, :select!, '() -> Enumerator<t>'
RDL.type :Array, :shift, '() -> t'
RDL.type :Array, :shift, '(Integer) -> Array<t>'
RDL.type :Array, :shuffle, '() -> Array<t>'
RDL.type :Array, :shuffle!, '() -> Array<t>'
RDL.rdl_alias :Array, :size, :length
RDL.rdl_alias :Array, :slice, :[]
RDL.type :Array, :slice!, '(Range<Integer>) -> Array<t>'
RDL.type :Array, :slice!, '(Integer, Integer) -> Array<t>'
RDL.type :Array, :slice!, '(Integer or Float) -> t'
RDL.type :Array, :sort, '() -> Array<t>'
RDL.type :Array, :sort, '() { (t,t) -> Integer } -> Array<t>'
RDL.type :Array, :sort!, '() -> Array<t>'
RDL.type :Array, :sort!, '() { (t,t) -> Integer } -> Array<t>'
RDL.type :Array, :sort_by!, '() { (t) -> u } -> Array<t>'
RDL.type :Array, :sort_by!, '() -> Enumerator<t>'
RDL.type :Array, :take, '(Integer) -> Array<t>'
RDL.type :Array, :take_while, '() { (t) ->%bool } -> Array<t>'
RDL.type :Array, :take_while, '() -> Enumerator<t>'
RDL.type :Array, :to_a, '() -> Array<t>'
RDL.type :Array, :to_ary, '() -> Array<t>'
RDL.rdl_alias :Array, :to_s, :inspect
RDL.type :Array, :transpose, '() -> Array<t>'
RDL.type :Array, :uniq, '() -> Array<t>'
RDL.type :Array, :uniq!, '() -> Array<t>'
RDL.type :Array, :unshift, '(*t) -> Array<t>'
RDL.type :Array, :values_at, '(*Range<Integer> or Integer) -> Array<t>'
RDL.type :Array, :zip, '(*Array<u>) -> Array<Array<t or u>>'
RDL.type :Array, :|, '(Array<u>) -> Array<t or u>'
