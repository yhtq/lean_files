import Mathlib
-- 1. Since $G$ is a $p$-group, $Z(G) \gt 1$
-- 2. Since $G$ is not abelian $Z(G) \lt G$. So $|Z(G)| = p$ or $p^2$.
-- 3. If $|Z(G)| = p^2$, then $G/Z(G)$ would be a cyclic group of order $p$ and thus implying $G$ is abelian.
-- 4. So we must have $|Z(G)| = p$; thus $G/Z(G)$ is a group of order $p^2$ and hence abelian (One should verify that for prime $p$ all groups of order $p^2$ are abelian.). Then $G' \subseteq Z(G)$ since $G'$ is smallest normal subgroup of $G$ whose quotient is abelian.
-- 5. Since $G$ is nonabelian, $G' \gt 1$ and this forces $G' = Z(G)$
theorem group_of_order_p3_center_eq_commutor
    (G: Type*) [Group G] [Finite G]
    {p: ℕ} [hp: Fact (p.Prime)]
    (hG: Nat.card G = p ^ 3)
    (not_abliean: CommGroup G -> False)
    :
    commutator G = Subgroup.center G := by
      letI is_p: IsPGroup p G := IsPGroup.of_card hG
      letI : Nontrivial G := by
        rw [<-Finite.one_lt_card_iff_nontrivial]
        rw [hG]
        simp
        exact Nat.Prime.one_lt hp.out
      have : (Nat.card $ Subgroup.center G) ∣ p^3 := by
        rw [<-hG]
        exact Subgroup.card_subgroup_dvd_card (Subgroup.center G)
      let ⟨k, ⟨hk1, hk2⟩⟩ := (Nat.dvd_prime_pow hp.out).mp this
      -- k = 0, 1, 2, 3
      interval_cases k
      · -- k = 0
        have := IsPGroup.center_nontrivial is_p  -- center of G is nontrivial
        rw [<-Finite.one_lt_card_iff_nontrivial, hk2] at this
        simp at this
      · -- k = 1,  $G/Z(G)$ is a group of order $p^2$ and hence abelian
        have quotient_card: Nat.card (G ⧸ Subgroup.center G) = p^2 := by
          have : p^3 = Nat.card (G ⧸ Subgroup.center G) * p := by
            rw [<-hG, show p = p^1 from (pow_one p).symm, <-hk2]
            exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
          rw [show p^3 = p^2 * p  by exact rfl] at this
          apply Nat.mul_right_cancel (Nat.pos_of_neZero p) this.symm
        letI := IsPGroup.commGroupOfCardEqPrimeSq quotient_card
        -- commutator is contained in ker f for every group homomorphism f from G to an abelian group
        have := Abelianization.commutator_subset_ker (QuotientGroup.mk' (Subgroup.center G))
        simp at this
        have := Subgroup.card_dvd_of_le this
        rw [hk2] at this
        simp only [pow_one, Nat.dvd_prime hp.out] at this
        rcases this with h | h
        -- subgroup of order p group is either trivial or the group itself
        · have : commutator G = ⊥ := Subgroup.eq_bot_of_card_eq (commutator G) h
          -- if commutator G = ⊥,then group is abelian
          rw [commutator_def] at this
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at this
          simp at this
          letI := Group.commGroupOfCenterEqTop this
          exact False.elim (not_abliean this)
        · have : commutator G = Subgroup.center G := by
            apply Subgroup.eq_of_le_of_card_ge this
            rw [h, hk2]
            simp
          exact this
      · -- k = 2
        have quotient_card: Nat.card (G ⧸ Subgroup.center G) = p := by
          have : p ^ 3 = Nat.card (G ⧸ Subgroup.center G) * p ^ 2 := by
            rw [<-hG, <-hk2]
            exact Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
          rw [show p^3 = p * p^2  from Nat.pow_succ'] at this
          apply Nat.mul_right_cancel (Nat.pos_of_neZero (p ^ 2)) this.symm
        exfalso
        apply not_abliean
        letI : IsCyclic (G ⧸ Subgroup.center G) := by
          apply isCyclic_of_card_dvd_prime (p := p)
          rw [quotient_card]
        -- show G is abelian
        apply commGroupOfCyclicCenterQuotient (QuotientGroup.mk' (Subgroup.center G))
        simp
      · -- k = 3, then center is ⊤, group G is abelian
        have : Subgroup.center G = ⊤ := by
          apply Subgroup.eq_top_of_card_eq
          rw [hk2, hG]
        exfalso
        apply not_abliean
        exact Group.commGroupOfCenterEqTop this
