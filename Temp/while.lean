
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/--
  We prove it by induction on `Nat` to avoid use the classical rule `¬ ¬ q -> q`
-/
lemma Nat.not_ne_zero {a : Nat} : ¬ a ≠ 0 -> a = 0 :=
  fun h1 =>
    match a with
    | 0 => rfl
    | Nat.succ n =>
      False.elim $ h1 (Nat.succ_ne_zero n)
/--
  A while loop in imperative style
-/
def While
  (S : Type*) -- the type of state.
  -- The following example will show that, we can use this type to carry the state and loop invariant at the same time
  (cond : S -> Prop)  -- the loop condition
  [DecidablePred cond]
  (body : (s : S) -> (cond s) -> S) -- the body is a statement which executes with the condition holds
  (decreasing : WellFoundedRelation S)  -- the decreasing relation
  (decreasing_proof : ∀ (s : S) (hs : cond s), decreasing.rel (body s hs) s) -- the proof of the decreasing relation
    : S -> {s : S // ¬cond s}
    -- finally we get a state s such that ¬cond s
    -- Here the `{s : S // ¬cond s}` is similar to a refinement of type `s` (but actually not, lean will not recognize it as a true subtype, but only do coercion)
  := fun x =>
    if h : cond x then
      let y := body x h
      While S cond body decreasing decreasing_proof y
    else ⟨x, h⟩
termination_by s => s
decreasing_by exact decreasing_proof _ _

/--
  Actually, the `While` above is executable
-/
def while_example (n : Nat) : Nat :=
  While
    (S := Nat)
    (fun n => n > 1000)
    (fun n _ => n / 2 - 1)
    (decreasing := Nat.lt_wfRel)
    (decreasing_proof := by
      intro n1 h
      simp
      show n1 / 2 - 1 < n1
      apply lt_of_le_of_lt (Nat.sub_le _ _) (Nat.div_lt_self (n := n1) (k := 2) (by omega) (by decide))
      )
    n

#eval while_example 10000

/--
  An "imperative" style proof of `nat_add_zero` using a while loop.
  We don't use any pattern match on `Nat` or recursion, but use a while loop, continuously decrement the number until it reaches 0.
  The loop invariant is `0 + n = n -> 0 + a = a`, and the loop condition is `n ≠ 0`.
  Also, only Martin-Löf style theorem and nothing about automation are used for a better transferability.
-/
def nat_add_zero {a : Nat} : 0 + a = a :=
  -- we use a while loop to prove this instead of induction
  let while_result :=
    While
      (S := {n : Nat // 0 + n = n -> 0 + a = a})  -- here the state is both the `symbolic state` and the `loop invariant`
      (fun s => s.1 ≠ 0)  -- the `loop condition` is that the number is greater than 0
      (body :=
        fun s h =>
          -- we have the hypothesis `h` that `n` is greater than 0
          let ⟨n, hn⟩ := s  -- get the `n` and condition on `n`
          ⟨n.pred, -- the body of the loop is to decrement the number

           -- and we need to prove the invariant, i.e. `0 + n.pred = n.pred -> 0 + a = a`
           -- actually, we only need to prove `0 + n.pred = n.pred -> 0 + n = n`
           fun hnpred =>
            -- assume `0 + n.pred = n.pred`
            -- by definition, `0 + n.pred.succ` is equivalent to `(0 + n.pred).succ`
            let add_destruct : 0 + n.pred.succ = (0 + n.pred).succ := rfl
            -- and by `n ≠ 0`, we have `n.pred.succ = n`
            let pred_succ : n.pred.succ = n := Nat.succ_pred h
            -- use the congruence lemma to get `0 + n = 0 + n.pred.succ`
            let add_destruct2 : 0 + n = 0 + n.pred.succ := congrArg (fun x => 0 + x) pred_succ.symm
            -- transitivity of equality gives `0 + n = (0 + n.pred).succ`
            let add_destruct3 : 0 + n = (0 + n.pred).succ := Eq.trans add_destruct2 add_destruct
            -- again, use the congruence lemma to get `(0 + n.pred).succ = n.pred.succ`
            let npred_succ : (0 + n.pred).succ = n.pred.succ := congrArg (fun x => x.succ) hnpred
            -- finally, use the transitivity to get the result
            hn $ Eq.trans add_destruct3 (
              Eq.trans npred_succ pred_succ
            )
          ⟩
      )
      (decreasing := invImage (fun x => x.val) Nat.lt_wfRel)  -- use less than as the decreasing relation
      (decreasing_proof := fun _ h =>
        Nat.pred_lt h
      )
      ⟨a, id⟩ -- the initial state is `a` and the invariant is trivially true
  let ⟨⟨n, invar⟩, not_cond⟩ := while_result
  -- finally, we get the invariant `0 + n = n → 0 + a = a` and the condition `¬(n ≠ 0)`
  let n_is_zero : n = 0 := Nat.not_ne_zero not_cond
  invar (
    -- here we only need to prove `0 + n = n` with `n = 0`
    let zero_add_n : 0 + n = 0 + 0 :=
      congrArg (fun x => 0 + x) n_is_zero
    Eq.trans zero_add_n (
      Eq.trans (rfl : 0 + 0 = 0) n_is_zero.symm
    )
  )
#print axioms nat_add_zero


/--
  A non-computable example: any set of vectors can be extended to generators in vector space with finite dimension.
-/
noncomputable def extend_vectors
  {F V : Type*}
  [Field F]
  [AddCommGroup V]
  [Module F V]
  [FiniteDimensional F V]
  (vs : Set V) :
    {gs : Set V // Submodule.span F (vs ∪ gs) = ⊤} :=  -- the vector space generated by `vs ++ gs` is the whole space
  -- here we must use `Classical.decPred` because the condition is not decidable normally
  letI : DecidablePred fun gs ↦ Submodule.span F (vs ∪ gs) = ⊤ := Classical.decPred _
  let while_result := While
    (S := Set V)
    (cond := fun gs => Submodule.span F (vs ∪ gs) ≠ ⊤)  -- when the span is not the whole space
    (body := fun gs hgs =>
      -- by definition, we have `¬∀ (x : V), x ∈ Submodule.span F (vs ∪ gs)`
      -- and we can use a classical rule to get `∃ (x : V), x ∉ Submodule.span F (vs ∪ gs)`
      let hgs2 := Classical.not_forall.mp $ (Iff.not Submodule.eq_top_iff').mp hgs
      -- and `Classical.choose` (which is result of axiom of choice) to get a "ghost" vector `x` from the symbolic state
      let x := Classical.choose hgs2
      Set.insert x gs
    )
    sorry -- ignore the decreasing relation here
    sorry
    vs
  let ⟨gs, hgs⟩ := while_result
  ⟨gs, Decidable.not_not.mp hgs⟩


/--
  An alternative version of less than relation, defined as:
  ```
  while (n != 0 && m != 0)
    n := n - 1
    m := m - 1
  return !(m == 0)
  ```
-/
def my_nat_lt (n m : Nat) : Bool :=
  let while_result := While
    (S := Nat × Nat)
    (cond := fun ⟨n, m⟩ => m ≠ 0 ∧ n ≠ 0)
    (body := fun ⟨n, m⟩ _ =>
      ⟨n - 1, m - 1⟩
    )
    (decreasing := invImage (fun x => x.1) Nat.lt_wfRel)  -- decreasing on `m`
    (decreasing_proof := fun _ h =>
      Nat.pred_lt h.2
    )
  let ⟨⟨_, m⟩, _⟩ := while_result (n, m)
  !(m == 0)

-- prove that `my_nat_lt` is equivalent to `n < m`
theorem my_lt_iff_lt {n m : Nat} : my_nat_lt n m = true ↔ n < m := by
  let while_result := While
    (S := {nm : Nat × Nat // (my_nat_lt nm.1 nm.2 = true <-> my_nat_lt n m = true) ∧ (nm.1 < nm.2 <-> n < m)})
    (cond := fun ⟨⟨n, m⟩, _⟩ => m ≠ 0 ∧ n ≠ 0)
    (body := fun ⟨⟨n1, m1⟩, hm1n1⟩ m1n1_cond =>
      ⟨⟨n1 - 1, m1 - 1⟩, -- in loop body, we make n := n - 1 and m := m - 1
        by
          simp only [<- hm1n1, Bool.coe_iff_coe]
          simp only [ne_eq] at *
          unfold my_nat_lt
          simp
          constructor
          ·
            conv =>
              rhs
              unfold While  -- we unfold the while loop of the right side, which is similar to one loop unrolling
            simp [m1n1_cond]  -- and the rest part is trivial
          · constructor <;> omega -- just some arithmetic facts
      ⟩
    )
    (decreasing := invImage (fun x => x.1.1) Nat.lt_wfRel)  -- decreasing on `m`
    (decreasing_proof := fun _ h =>
      Nat.pred_lt h.2
    )
    -- and the initial state
    ⟨⟨n, m⟩, by simp⟩
  let ⟨⟨⟨n1, m1⟩, hm1⟩, n1m1_cond⟩ := while_result
  simp at hm1
  rw [<-hm1.1, <-hm1.2]
  simp only [ne_eq, Decidable.not_and_iff_or_not, Decidable.not_not] at n1m1_cond
  unfold my_nat_lt
  rcases n1m1_cond with h | h <;> simp [h] <;> unfold While <;> simp  -- also after unfolding and unrolling, only some arithmetic facts are left
  exact Nat.ne_zero_iff_zero_lt
