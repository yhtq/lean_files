import Lean

open Lean.Meta Lean

-- elab "explore" : tactic => do
--   let mvarId : MVarId ← Lean.Elab.Tactic.getMainGoal
--   let metavarDecl : MetavarDecl ← mvarId.getDecl

--   IO.println "Our metavariable"
--   IO.println s!"{<- mvarId.getType}"

--   IO.println "All of its local declarations"
--   mvarId.withContext do
--     let target ← mvarId.getType
--     for localDecl in <- getLCtx do
--       if localDecl.isImplementationDetail then
--         continue
--       IO.println s!"{localDecl.userName}"
--       if <- isDefEq target localDecl.type then
--         IO.println "This is the target"
--         mvarId.assign localDecl.toExpr
--       else
--         IO.println "This is not the target"
--   -- ...

-- theorem red (hA : 1 = 1) (hB : 2 = 2) : 2 = 2 := by
--   apply? using hA
--   explore
--   sorry
-- #check red
#eval show Lean.Elab.Term.TermElabM _ from do
  let mvar1 <- mkFreshExprMVar (mkConst `Nat [])
  let mvar2 <- mkFreshExprMVar (mkConst `Nat [])
  let one := Expr.lit (Lean.Literal.natVal 1)
  let one' := Expr.app (Expr.const ``Nat.succ []) (Expr.const ``Nat.zero [])
  let printMVars: MetaM Unit := do
    IO.println s!"mvar1: {<- instantiateMVars mvar1}"
    IO.println s!"mvar2: {<- instantiateMVars mvar2}"
  let exp1 := mkAppN (mkConst `Nat.add) #[mvar1, .const `Nat.zero []]
  let exp2 := mkAppN (mkConst `Nat.add) #[mvar2, .const `Nat.zero []]
  let state <- saveState
  printMVars
  if <- isDefEq one one' then
    IO.println "They are equal"
  else
    IO.println "They are not equal"
  printMVars
  restoreState state
  printMVars
#eval show Lean.Elab.Term.TermElabM _ from do
  let stx : Syntax ← `(∀ (a : Prop) (b : Prop), a ∨ b → b → a ∧ a)
  let expr ← Elab.Term.elabTermAndSynthesize stx none

  let (_, _, conclusion) ← forallMetaTelescope expr
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← forallMetaBoundedTelescope expr 2
  dbg_trace conclusion -- ...

  let (_, _, conclusion) ← lambdaMetaTelescope expr
  dbg_trace conclusion -- ...
