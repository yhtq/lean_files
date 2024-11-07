import Mathlib




open Fintype Filter Equiv Subgroup

--If P is a Sylow_p subgroup of G, we have k ∈ ℕ, |P| = p ^ k ∣|G|, and p ^ (k + 1) ∤ |G|.
--If P ≤ H ≤ G, we have |P| = p ^ k ∣|H|, and p ^ (k + 1) ∤ |H|, which is simply proved by p ^ (k + 1) ∤ |G|.
--So P is a Sylow_p subgroup of H.
example [Group G] [hp : Fact p.Prime] (P : Sylow p G) (H : Subgroup G) (h : ↑P ≤ H) : Sylow p H := by
  exact P.subtype h

--We have K4 as a subgroup of A4.
abbrev Klein_subgroup : Subgroup (Equiv.Perm (Fin 4)) := {
  carrier := {c[1] , c[1, 2]*c[3,4],c[1,3]*c[2,4], c[1,4]*c[2,3]}
  one_mem' := by
    simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_singleton, List.formPerm_cons_cons,
      mul_one, Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
  mul_mem' :=  by
    simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_singleton, List.formPerm_cons_cons,
      mul_one, Set.mem_insert_iff, Set.mem_singleton_iff]
    all_goals decide
  inv_mem' := by
    simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_singleton, List.formPerm_cons_cons,
      mul_one, Set.mem_insert_iff, Set.mem_singleton_iff, inv_eq_one, forall_eq_or_imp, inv_one,
      true_or, Equiv.swap_eq_one_iff, Fin.reduceEq, Equiv.swap_inv, self_eq_mul_right, or_false,
      or_true, self_eq_mul_left, forall_eq, mul_inv_rev, mul_left_eq_self, mul_right_eq_self,
      false_or, true_and]
    all_goals decide
}

lemma Klein_card : Fintype.card Klein_subgroup = 4 := by decide

theorem subgroup_A4 : Klein_subgroup ≤ (alternatingGroup (Fin 4)) := by
  have : ∀ ⦃x : Equiv.Perm (Fin 4)⦄, x ∈ Klein_subgroup → x ∈ alternatingGroup (Fin 4) := by
    intro x hx
    have : x = c[1] ∨ x = (swap 1 2)*(swap 3 4)∨ x = (swap 1 3)*(swap 2 4) ∨ x = (swap 1 4)*(swap 2 3) := by
      simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_singleton, List.formPerm_cons_cons,
        mul_one]
      exact hx
    simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_singleton] at this
    rcases this with x1|x1|x1|x1
    · exact (QuotientGroup.eq_one_iff x).mp (congrArg QuotientGroup.mk x1)
    · refine Subgroup.mem_carrier.mp ?inr.inl.a
      exact Set.mem_of_eq_of_mem x1 rfl
    · refine Subgroup.mem_carrier.mp ?inr.inr.inl.a
      exact Set.mem_of_eq_of_mem x1 rfl
    · refine Subgroup.mem_carrier.mp ?inr.inr.inr.a
      exact Set.mem_of_eq_of_mem x1 rfl
  exact this



--we need to prove that K4 is a Sylow_2 subgroup of A4, but not a Sylow_2 subgroup of S4
example : ∃ K : Sylow 2 (alternatingGroup (Fin 4)), K = Klein_subgroup.subgroupOf (alternatingGroup (Fin 4)) := by
  classical
  --Simply we know that |K4| = 4, |A4| = 8 ,so it's a Sylow-2 subgroup of |A4|.
  let K := Klein_subgroup.subgroupOf (alternatingGroup (Fin 4))
  have sub : Klein_subgroup ≤ (alternatingGroup (Fin 4)) := by exact subgroup_A4
  have card_K : card K = card Klein_subgroup := by
    have : K ≃* Klein_subgroup := by exact subgroupOfEquivOfLe sub
    apply Fintype.card_congr this
  have card_K4 : card Klein_subgroup = 4 := by convert Klein_card
  have card_Sylow: card K = 2 ^ Nat.factorization (card (alternatingGroup (Fin 4))) 2 := by
    have : card (alternatingGroup (Fin 4)) = 12 := by
      simp only [Equiv.Perm.mem_alternatingGroup]
      exact rfl
    rw [this]
    have : (Nat.factorization 12) 2 = 2 := by
      rw [← Nat.factors_count_eq]
      exact rfl
    rw [this]
    norm_num
    rw [card_K]
    exact card_K4
  let K' : Sylow 2 (alternatingGroup (Fin 4)) := Sylow.ofCard K card_Sylow
  use K'
  exact rfl


example [IsCancelMul ℕ] : (∃ K : Sylow 2 (Equiv.Perm (Fin 4)), K = Klein_subgroup) → False := by
  --We prove that K4 is not a Sylow-2 subgroup of S4.
  classical
  intro h
  rcases h with ⟨K, hk⟩
  have : card ((Equiv.Perm (Fin 4))⧸ Klein_subgroup) * card Klein_subgroup = Fintype.card (Equiv.Perm (Fin 4)) := by
    exact Eq.symm (Subgroup.card_eq_card_quotient_mul_card_subgroup Klein_subgroup)
  have card_K4 : card Klein_subgroup = 4 := by convert Klein_card
  have card_S4 : card (Equiv.Perm (Fin 4)) = 24 := by
    exact rfl
  rw [card_K4, card_S4] at this
  have card_quot : card (Equiv.Perm (Fin 4) ⧸ Klein_subgroup) = 6 := by
    have simp_dvd : 24 = 6 * 4 := by simp only [Nat.reduceMul]
    rw [simp_dvd] at this
    apply mul_right_cancel at this
    exact this
  have : Klein_subgroup.index = 6 := by
    rw [← card_quot]
    apply Subgroup.index_eq_card
  --It's obvious because |K4| = 4 but 8 ∣ |S4| = 24.
  have coprime : Nat.Coprime (Fintype.card Klein_subgroup) (Klein_subgroup.index ) := by
    convert Sylow.card_coprime_index K <;> rw [hk]
  rw [card_K4, this] at coprime
  have notcoprime : ¬ Nat.Coprime 4 6 := by
    exact Nat.succ_succ_ne_one 0
  exact notcoprime coprime
