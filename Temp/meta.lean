-- import Mathlib

-- example : 0 <= 1 := by
--     #leansearch "0 <= 1?"

-- macro "nat_le" : tactic => do
--     `(tactic| repeat (first | apply Nat.le_refl | apply Nat.le_step))
-- #leansearch "111"
import Lean
open Lean Meta Elab Tactic
elab "TODO" t:str : tactic =>
    withMainContext do
        let g <- getMainTarget
        logInfo m!"TODO: {t}"
        let pf <- mkAppM ``sorryAx #[g, mkConst ``false]
        closeMainGoal `todo pf
        return
