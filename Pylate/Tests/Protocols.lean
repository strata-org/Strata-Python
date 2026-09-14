import Pylate.Transfers.Protocols

namespace Pylate.Tests.Protocols

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Protocols

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9961, 1, 0⟩

def services : Protocols.Services where
  resolveMethod := fun _ _ => pure none
  invokeUser := fun _ _ _ _ _ _ => pure {}
  generatorExceptions := fun _ => pure []

def run (name : String) (arguments : List AbsVal) :
    Flow × Actx :=
  (execute services position name arguments [] {}).run
    { policy := Policy.audit }

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def testUnknownProtocols : IO Unit := do
  let (length, _) := run "len" [anyV]
  ensure length.normal.isSome
    "len(any) lost feasible normal completion"
  ensure (hasRaised length "TypeError")
    "len(any) omitted feasible TypeError"

  let (iterator, _) := run "iter" [anyV]
  ensure iterator.normal.isSome
    "iter(any) lost feasible normal completion"
  ensure (hasRaised iterator "TypeError")
    "iter(any) omitted feasible TypeError"

  let (nextValue, _) := run "next" [anyV]
  ensure nextValue.normal.isSome
    "next(any) lost feasible normal completion"
  ensure (hasRaised nextValue "TypeError")
    "next(any) omitted feasible TypeError"
  ensure (hasRaised nextValue "StopIteration")
    "next(any) omitted feasible StopIteration"

  let (nextDefault, _) := run "next" [anyV, V [.tstr]]
  ensure nextDefault.normal.isSome
    "next(any, default) lost normal completion"
  ensure (hasRaised nextDefault "TypeError")
    "next(any, default) omitted feasible TypeError"
  ensure (!hasRaised nextDefault "StopIteration")
    "next(any, default) leaked handled StopIteration"

def runAll : IO Unit := do
  testUnknownProtocols
  IO.println "RuleProtocols tests passed"

end Pylate.Tests.Protocols
