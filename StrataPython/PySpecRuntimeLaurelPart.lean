/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataLaurel.Implementation.Grammar.LaurelGrammar
import StrataLaurel.Implementation.Grammar.ConcreteToAbstractTreeTranslator
public import StrataLaurel.Implementation.LaurelAST
public import StrataDDM.AST
public import StrataDDM.Integration.Lean.HashCommands -- shake: keep

open Strata
namespace StrataPython

/-- Contract-only logical dictionary model and recursive Python equality. -/
def pySpecRuntimeLaurelPartDDM :=
#strata
program Laurel;

datatype PySpecDictValue {
  Missing (),
  Present (value: Any)
}

// A deterministic hole in a transparent body lowers to one uninterpreted
// function of d. Repeated views of the same runtime dictionary are therefore
// equal, unlike repeated calls to a declaration-only opaque procedure.
procedure PySpecDict_modelOf (d : DictStrAny) : TotalMap string PySpecDictValue
return <?>;

procedure PySpecDict_modelOf_boxed (d : DictStrAny)
  invokeOn PySpecDict_modelOf(Any..as_Dict!(from_DictStrAny(d)))
  opaque
  ensures PySpecDict_modelOf(Any..as_Dict!(from_DictStrAny(d))) ==
    PySpecDict_modelOf(d)
  ensures DictStrAny..isDictStrAny_empty(d) ||
    select(
      PySpecDict_modelOf(Any..as_Dict!(from_DictStrAny(d))),
      DictStrAny..key!(d)) == Present(DictStrAny..val!(d));

procedure PySpecDict_modelOf_empty (key: string)
  invokeOn select(PySpecDict_modelOf(DictStrAny_empty()), key)
  opaque
  ensures select(PySpecDict_modelOf(DictStrAny_empty()), key) == Missing();

procedure PySpecDict_modelOf_cons (key: string, value: Any, tail: DictStrAny)
  invokeOn PySpecDict_modelOf(DictStrAny_cons(key, value, tail))
  opaque
  ensures PySpecDict_modelOf(DictStrAny_cons(key, value, tail)) ==
    update(PySpecDict_modelOf(tail), key, Present(value))
  ensures select(PySpecDict_modelOf(DictStrAny_cons(key, value, tail)), key) ==
    Present(value);

procedure PySpecDict_modelOf_insert (d : DictStrAny, key: string, value: Any)
  invokeOn PySpecDict_modelOf(DictStrAny_insert(d, key, value))
  opaque
  ensures PySpecDict_modelOf(DictStrAny_insert(d, key, value)) ==
    update(PySpecDict_modelOf(d), key, Present(value))
  ensures select(PySpecDict_modelOf(DictStrAny_insert(d, key, value)), key) ==
    Present(value);

procedure PySpecDict_modelOf_remove (d : DictStrAny, key: string)
  invokeOn PySpecDict_modelOf(DictStrAny_remove(d, key))
  opaque
  ensures PySpecDict_modelOf(DictStrAny_remove(d, key)) ==
    update(PySpecDict_modelOf(d), key, Missing())
  ensures select(PySpecDict_modelOf(DictStrAny_remove(d, key)), key) ==
    Missing();

procedure PySpecDict_modelOf_lookup (d : DictStrAny, key: string)
  invokeOn DictStrAny_contains(d, key)
  opaque
  ensures select(PySpecDict_modelOf(d), key) ==
    (if DictStrAny_contains(d, key)
     then Present(DictStrAny_get_or_none(d, key))
     else Missing());

procedure PySpecDict_modelOf_lookup_get (d : DictStrAny, key: string)
  invokeOn DictStrAny_get(d, key)
  opaque
  ensures select(PySpecDict_modelOf(d), key) ==
    (if DictStrAny_contains(d, key)
     then Present(DictStrAny_get_or_none(d, key))
     else Missing());

// Walk the representation structurally so termination is explicit. `seen`
// skips duplicate nodes while preserving first-key-wins lookup semantics.
procedure PySpecDict_subsetScalarEq(
  left: DictStrAny, right: DictStrAny, seen: TotalMap string PySpecDictValue) : bool
return if DictStrAny..isDictStrAny_empty(left)
  then true
  else if PySpecDictValue..isPresent(select(seen, DictStrAny..key!(left)))
    then PySpecDict_subsetScalarEq(DictStrAny..tail!(left), right, seen)
    else DictStrAny_contains(right, DictStrAny..key!(left)) &&
      PySpecAny_scalarEq(
        DictStrAny..val!(left),
        DictStrAny_get(right, DictStrAny..key!(left))) &&
      PySpecDict_subsetScalarEq(
        DictStrAny..tail!(left),
        right,
        update(seen, DictStrAny..key!(left), Present(from_None())));

procedure PySpecDict_scalarEq(left: DictStrAny, right: DictStrAny) : bool
return <?>;

// Keep dictionary equality deterministic while specifying it outside the
// executable call graph, so nested Any/dictionary equality has no cyclic
// same-size termination edge.
procedure PySpecDict_scalarEq_def(left: DictStrAny, right: DictStrAny)
  invokeOn PySpecDict_scalarEq(left, right)
  opaque
  ensures PySpecDict_scalarEq(left, right) ==
    (PySpecDict_subsetScalarEq(
      left, right, PySpecDict_modelOf(DictStrAny_empty())) &&
    PySpecDict_subsetScalarEq(
      right, left, PySpecDict_modelOf(DictStrAny_empty())));

procedure PySpecList_scalarEq(left: ListAny, right: ListAny) : bool
return if ListAny..isListAny_nil(left)
  then ListAny..isListAny_nil(right)
  else !ListAny..isListAny_nil(right) &&
    PySpecAny_scalarEq(ListAny..head!(left), ListAny..head!(right)) &&
    PySpecList_scalarEq(ListAny..tail!(left), ListAny..tail!(right));

procedure PySpecAny_scalarEq(left: Any, right: Any) : bool
return if Any..isexception(left) || Any..isexception(right)
  then false
  else if Any..isfrom_DictStrAny(left)
  then Any..isfrom_DictStrAny(right) &&
    PySpecDict_scalarEq(Any..as_Dict!(left), Any..as_Dict!(right))
  else if Any..isfrom_DictStrAny(right)
    then false
  else if Any..isfrom_ListAny(left)
    then Any..isfrom_ListAny(right) &&
      PySpecList_scalarEq(Any..as_ListAny!(left), Any..as_ListAny!(right))
  else if Any..isfrom_ListAny(right)
    then false
  else Any_to_bool(PEq(left, right));

#end

public def pySpecRuntimeLaurelPart : Laurel.Program :=
  match Laurel.TransM.run
      (.file "StrataPython/PySpecRuntimeLaurelPart.lean")
      (Laurel.parseProgram pySpecRuntimeLaurelPartDDM) (synthesized := true) with
  | .ok p => p
  | .error e =>
    panic! s!"SOUND BUG: Failed to parse PySpec runtime Laurel part: {e}"

end StrataPython
