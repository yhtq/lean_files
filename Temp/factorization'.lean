import Init.Data.Nat.Basic
import Mathlib.NumberTheory.Padics.PadicVal
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Eval
import Batteries.Data.LazyList
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Logic.Equiv.Defs
example : (Nat.factorization 132) 2 = (eval% (Nat.factorization 132) 2) := by
  native_decide
def s : DecidablePred (fun n => 132 ∣ n) := inferInstance
def factorization' : Nat -> Nat -> Nat
  | 0, _ => 0
  | _, 0 => 0
  | _, 1 => 0
  | k + 1, s + 2 => if  (s+2) ∣ (k+1) then (factorization' ((k + 1) / (s + 2)) (s + 2)) + 1 else 0
termination_by  n _ => n
decreasing_by
  simp only
  unfold InvImage
  simp only
  simp_wf
  apply Nat.div_lt_self <;> simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true]

#eval factorization' 132 2
#eval Nat.log 2 132
example : Nat.log 2 132 = 7 := by
  repeat
    unfold Nat.log
    reduce
  decide
#check Nat.beq

unseal factorization'
example : factorization' 132 2 = 2 := by
  -- repeat
  --   unfold factorization'
  --   reduce
  -- rfl
  decide


example : padicValNat 2 132 = 2 := by
  native_decide

example  (n: ℕ) (h: n < 2) : n = 0 ∨ n = 1 := by
  revert h n
  decide
#reduce ∀ n < 2, n = 0 ∨ n = 1
#check Nat.le
#synth Group (Equiv.Perm (Fin 3))
example : (∀a b: Equiv.Perm (Fin 3), a * b = b * a) -> False := by
  intro a
  let c3: Equiv.Perm (Fin 3) :=  (Equiv.swap 0 1) *  (Equiv.swap 1 2)
  let c4: Equiv.Perm (Fin 3) :=  (Equiv.swap 1 2) * (Equiv.swap 0 1)
  have _: c3 = c4 := a _ _
  have _: c3 ≠ c4 := by
    unfold_let
    decide
  contradiction


def c1: Equiv.Perm (Fin 3) := c[0, 1]
def c2: Equiv.Perm (Fin 3) := c[1, 2]
#eval (c1 * c2)
