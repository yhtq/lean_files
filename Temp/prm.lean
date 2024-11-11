import Mathlib

-- the following code is the proof of a p-group has subgroup of index p,
-- which is enough to show a p-group has subgroup of every possible order
open Classical
noncomputable def p_group_has_a_normal_subgroup_of_index_p
    (G: Type*) [Group G] [Nontrivial G] [Finite G]
    {p: ℕ} [hp: Fact (p.Prime)]
    (is_p: IsPGroup p G):
    ∃ H: Subgroup G, H.Normal ∧ Subgroup.index H = p := by
      have has_a_nontrivial_normal_subgroup_deduces_result
        (H: Subgroup G) [H_normal: H.Normal]
        [nontrivial_H1: Nontrivial (G ⧸ H)]
        (nontrivial_H2: H ≠ ⊥)
        : ∃ H1: Subgroup G, H1.Normal ∧ Subgroup.index H1 = p := by
          -- this lemma is used to show the recursive termination
          have decreasing: Nat.card (G ⧸ H) < Nat.card G := by
            have := Subgroup.card_quotient_dvd_card H
            have := Nat.le_of_dvd (Nat.card_pos) this
            have : (Nat.card G) ≠ (Nat.card (G ⧸ H)) := by
              intro h
              have := Subgroup.card_eq_card_quotient_mul_card_subgroup H
              rw [h] at this
              norm_num [show (Nat.card (G ⧸ H) ≠ 0) by apply Nat.ne_zero_iff_zero_lt.mpr; exact Nat.card_pos] at this
              exact nontrivial_H2 this
            omega
          -- Recursively, we get a normal subgroup of index p in G/H
          let ⟨H1, ⟨H1_normal, H1_index⟩⟩ := p_group_has_a_normal_subgroup_of_index_p (G ⧸ H) (IsPGroup.to_quotient is_p _)
          let H2 := Subgroup.comap (QuotientGroup.mk' (H)) H1
          use H2
          constructor
          · infer_instance -- H is obviously normal
          · -- just need to show the index, notice that Quotient.mk is surjective, the index is very easy to calculate
            rw [Subgroup.index_comap_of_surjective]
            exact H1_index
            exact QuotientGroup.mk'_surjective (H)
      have := IsPGroup.center_nontrivial is_p
      by_cases h: Nontrivial (G ⧸ Subgroup.center G)
      · -- G/Z(G) is nontrivial, means G is not abliean
        exact has_a_nontrivial_normal_subgroup_deduces_result (Subgroup.center G) ((Subgroup.nontrivial_iff_ne_bot (Subgroup.center G)).mp this)
      · -- G/Z(G) is trivial, means G is abliean, we will use the structure theorem to get the result
        have : Subgroup.center G = ⊤ := by
          apply (Subgroup.eq_top_iff' (Subgroup.center G)).mpr
          intro x
          rw [<-QuotientGroup.eq_one_iff]
          -- not nontrivial means the quotient group is Subsingleton, in which every two elements are equal
          have : Subsingleton (G ⧸ Subgroup.center G) := not_nontrivial_iff_subsingleton.mp h
          exact Subsingleton.eq_one _
        letI := Group.commGroupOfCenterEqTop this -- G is abliean
        have := CommGroup.equiv_prod_multiplicative_zmod G  -- use the structure of abliean group
        let ⟨I, ⟨x, ⟨n, h⟩⟩⟩ := this
        let iso := h.2.some
        -- the canonical surjection, with some annoying transformation
        let proj (i: I) : G →* (Multiplicative (ZMod (n i))) := (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (n j))) i).comp iso
        have proj_surjective: ∀ i: I, Function.Surjective (proj i) := by
          intro i
          unfold_let proj
          simp
          intro y
          simp
          use (Pi.mulSingle i y)
          simp
        have card_eq := Nat.card_congr iso.toEquiv
        simp [Nat.card_pi, Multiplicative, Nat.card_zmod] at card_eq
        have is_p1: ∀i: I, IsPGroup p (Multiplicative $ ZMod (n i)) := by
          intro i
          apply IsPGroup.of_surjective is_p (proj i) (proj_surjective i)
        have : Nonempty I := by
          by_contra h
          simp at h
          have := Pi.uniqueOfIsEmpty (fun j => Multiplicative (ZMod (n j)))  -- if I is empty, the product is unique
          have := Equiv.unique iso.toEquiv  -- then G is unique
          apply not_nontrivial G
          infer_instance
        let i := this.some  -- random pick an element in I
        let proj_i := proj i
        haveI : Fintype G := Fintype.ofFinite G
        haveI : Fintype (Multiplicative (ZMod (n i))) := by
          -- the fintype instance need a non zero instance
          simp [Multiplicative]
          haveI : NeZero (n i) := by
            have := h.1 i
            exact NeZero.of_gt this
          infer_instance
        by_cases h1: Nat.card (Multiplicative (ZMod (n i))) = Nat.card G
        · -- if the order of the group is the same as the order of the factor, then group G is equiv to ZMod (n i)
          have : Function.Bijective proj_i := by
            apply (Fintype.bijective_iff_surjective_and_card _).mpr
            constructor
            · exact proj_surjective i
            · repeat rw [<-Nat.card_eq_fintype_card]
              exact h1.symm
          -- use this bijection to construct target group in ZMod (n i)
          have : G ≃* (Multiplicative (ZMod (n i))) := MulEquiv.ofBijective proj_i this
          -- show G is a cyclic group
          letI : IsCyclic G := by
            apply isCyclic_of_surjective (this.symm)
            exact MulEquiv.surjective this.symm
          -- manually construct the cyclic group of index p
          let ⟨g, hg⟩ := isCyclic_iff_exists_ofOrder_eq_natCard.mp this
          have order_pow := orderOf_pow g (n := p)
          simp only [hg] at order_pow
          have card_dvd : p ∣ Nat.card G := by
            have := IsPGroup.card_eq_or_dvd is_p
            have ne_one : Nat.card G ≠ 1 := by
              have := Finite.one_lt_card (α := G)
              omega
            simp only [ne_one, false_or] at this
            exact this
          have : (Nat.card G).gcd p = p := by
            apply Nat.gcd_eq_right
            exact card_dvd
          rw [this] at order_pow
          -- use the group generated by g^p
          use Subgroup.zpowers (g ^ p)
          constructor
          · infer_instance
          · -- do some annoying calculation
            have index_mul := Subgroup.card_mul_index (Subgroup.zpowers (g^p))
            rw [Nat.card_zpowers, order_pow] at index_mul
            -- transfer equation in N to Q
            qify [card_dvd] at index_mul
            apply_fun (fun (x) => ((Fintype.card G): ℚ)⁻¹ * x) at index_mul
            field_simp [show (p: ℚ) ≠ 0 by exact Ne.symm (NeZero.ne' _)] at index_mul
            exact index_mul
        ·
          -- other steps are the same as the previous case, we need the card equation to show the subgroup is non trivial
          let H := proj_i.ker
          have eq := QuotientGroup.quotientKerEquivOfSurjective proj_i (proj_surjective i)
          have : Nontrivial (Multiplicative (ZMod (n i))) := by
            rw [<-Finite.one_lt_card_iff_nontrivial]
            simp [Multiplicative, Nat.card_zmod]
            exact h.1 i
          have : Nontrivial (G ⧸ H) := by
            unfold_let H
            -- becases G ⧸ H is equiv to ZMod (n i), which is nontrivial
            apply Equiv.nontrivial (eq.toEquiv)
          apply has_a_nontrivial_normal_subgroup_deduces_result H
          -- show H ≠ ⊤
          intro h
          unfold_let H at h
          have := Subgroup.card_eq_card_quotient_mul_card_subgroup (proj_i.ker)
          nth_rw 2 [h] at this
          simp at this
          rw [Fintype.card_congr eq.toEquiv] at this
          simp [this] at h1
termination_by Nat.card G

#leansearch "the equiv from G to Subgroup.map?"

-- 1. Firstly, according to the Sylow theorem, there is a subgroup of order $p^r$
-- 2. Secondly, a P-group has subgroup of every possible order (the theorem above proves that any p-group has a subgroup of index p, recursively using of this proves the fact we need), which gives every subgroup we need.

theorem group_of_order_p_pow_r_mul_m_has_subgroup_p_pow_k
    {G: Type*} [Group G] [Finite G]
    {p: ℕ} [hp: Fact p.Prime]
    {r m: ℕ} (coprime: Nat.Coprime p m)
    (h_order: Nat.card G = p ^ r * m):
    ∀ k ≤ r, ∃H : Subgroup G, Nat.card H = p ^ k := by
      by_cases hr: r = 0
      · simp [hr] -- a trivial case

      have hr: r ≠ 0 := by omega
      let sylow_p: Sylow p G := default -- choose the default sylow p-subgroup
      have sylow_p_card := Sylow.card_eq_multiplicity sylow_p
      -- caculate the order of the sylow p-subgroup
      rw [h_order] at sylow_p_card
      haveI ne_p : NeZero p := by exact NeZero.of_gt'
      -- used for the following rewrite
      have : (p ^ r).Coprime m := Nat.Coprime.pow_left r coprime
      have : p ∈ (p ^ r).primeFactorsList := by simp [hp.out, ne_p.out]; exact dvd_pow_self p hr

      rw [Nat.factorization_eq_of_coprime_left] at sylow_p_card <;> try assumption
      simp [hp.out] at sylow_p_card
      intro k hk

      -- prepare for the following proof
      have sylow_p_is_p: IsPGroup p sylow_p := sylow_p.isPGroup'
      have : Nontrivial sylow_p := by
        rw [IsPGroup.nontrivial_iff_card sylow_p_is_p]
        use r
        omega
      have := p_group_has_a_normal_subgroup_of_index_p sylow_p sylow_p_is_p
      -- calculate the card of H which is a subgroup of sylow_p of index p
      rcases this with ⟨H, ⟨_, H_index⟩⟩
      have H_card := Subgroup.index_mul_card H
      rw [H_index, sylow_p_card] at H_card
      rw [show p ^ r = p * p ^ (r - 1) by exact Eq.symm (mul_pow_sub_one hr p)] at H_card
      norm_num  at H_card
      simp [show p ≠ 0 from Ne.symm (NeZero.ne' p)] at H_card

      have k_cond: k = r ∨ k = r - 1 ∨ k ≤ r - 2 := by omega  -- use for rcases
      rcases k_cond with hk | hk | hk
      · -- p^r subgroup is trivial
        use sylow_p
        exact hk ▸ sylow_p_card
      · -- p^(r-1) subgroup comes from the theorem proved above
        use Subgroup.map (Subgroup.subtype _) H -- use the map of canonical injection to pull the subgroup of sylow_p to subgroup of G
        rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv.symm]  -- use equiv to transfer the equation of card
        rw [hk]
        exact H_card
      · -- k <= r - 2, recursively use this theorem
        rw [show p^(r-1) = p^(r-1) * 1 from Eq.symm (Nat.mul_one (p ^ (r - 1)))] at H_card
        have := group_of_order_p_pow_r_mul_m_has_subgroup_p_pow_k (Nat.gcd_one_right p) H_card
        specialize this k (by omega)
        -- pull the subgroup of H to subgroup of G
        let ⟨H1, hH1⟩ := this
        use Subgroup.map ((Subgroup.subtype _).comp (Subgroup.subtype _)) H1
        rw [Nat.card_congr (Subgroup.equivMapOfInjective _ _ _).toEquiv.symm]
        exact hH1
        rw [MonoidHom.coe_comp]
        apply Function.Injective.comp <;> exact Subgroup.subtype_injective _
