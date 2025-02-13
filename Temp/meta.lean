import Mathlib

example : 10 <= 20 := by
    repeat (first | apply Nat.le_refl | apply Nat.le_step)

macro "nat_le" : tactic => do
    `(tactic| repeat (first | apply Nat.le_refl | apply Nat.le_step))
