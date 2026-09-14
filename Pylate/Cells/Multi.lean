/-
Statement outcomes: the five-mode record (normal, break, continue,
return, exception with a class set), the fixed continuation-token
treatment of Astree applied to the fragment.
-/
import Pylate.Cells.State

namespace Pylate

structure AMulti where
  normal : Option AState := none
  brk    : Option AState := none
  cont   : Option AState := none
  retSt  : Option AState := none
  retVal : AbsVal := AbsVal.bot
  excSt  : Option AState := none
  excs   : Fset String := []
deriving Repr, Inhabited

namespace AMulti

def ofNormal (st : AState) : AMulti := { normal := some st }

def join (a b : AMulti) : AMulti where
  normal := joinOpt a.normal b.normal
  brk    := joinOpt a.brk b.brk
  cont   := joinOpt a.cont b.cont
  retSt  := joinOpt a.retSt b.retSt
  retVal := a.retVal.join b.retVal
  excSt  := joinOpt a.excSt b.excSt
  excs   := Fset.union a.excs b.excs

def le (a b : AMulti) : Bool :=
  leOpt a.normal b.normal && leOpt a.brk b.brk && leOpt a.cont b.cont &&
  leOpt a.retSt b.retSt && a.retVal.le b.retVal &&
  leOpt a.excSt b.excSt && Fset.subset a.excs b.excs

/-- Abnormal modes only (everything but normal). -/
def abnormalOf (a : AMulti) : AMulti := { a with normal := none }

end AMulti

end Pylate
