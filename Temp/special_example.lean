import Std
import Mathlib.Data.Finset.Basic
-- import Mathlib.Algebra.BigOperators.Group.Finset
import Lean
import Batteries.Util.ExtendedBinder
open Nat Lean Batteries.ExtendedBinder
-- syntax (name := bigsumin) "Σ" term "in" term "," term: term

-- #check Finset.sum

-- partial def denoteBigsumin : TSyntax `bigsumin -> Nat
--   | `(bigsumin | Σ $x in $s, $f) =>
-- -- our "elaboration function" that infuses syntax with semantics
-- @[term_elab bigsumin] def elabSum : TermElab := sorry
-- Note: std4 has to be in dependencies of your project for this to work.
syntax (name := bigsumin) "∑ " extBinder "in " term "," term : term

@[term_elab bigsumin]
def elabSum : TermElab := do


#eval ∑ x in { 1, 2, 3 }, x^2

def hi := (∑ x in { "apple", "banana", "cherry" }, x.length) + 1
#eval hi
