import Mathlib

theorem MvPolynomial.coeff_mul_C {R : Type u} {σ : Type u_1} [CommSemiring R] (m : σ →₀ ℕ) (a : R) (p : MvPolynomial σ R) :
MvPolynomial.coeff m (p * MvPolynomial.C a) = a * MvPolynomial.coeff m p := by
  rw [<-MvPolynomial.coeff_C_mul, mul_comm]

@[simp]
theorem MvPolynomial.iterToSum_C (R S₁ S₂ : Type*) [CommSemiring R] (p : MvPolynomial S₂ R) :
  (MvPolynomial.iterToSum R S₁ S₂ (MvPolynomial.C p)) = MvPolynomial.rename (Sum.inr) p := by
    apply MvPolynomial.induction_on p <;> aesop

-- theorem Finset.prod_sum_type {A B C : Type*} [DecidableEq A] [DecidableEq B] [CommMonoid C] {s: Finset (A ⊕ B)} {f : (A ⊕ B) -> C} :
--   s.prod f =
--     (s.toLeft.prod (f ∘ Sum.inl)) * (s.toRight.prod (f ∘ Sum.inr)) := by
--       apply Finset.induction (
--         p := fun s => s.prod f = (s.toLeft.prod (f ∘ Sum.inl)) * (s.toRight.prod (f ∘ Sum.inr))
--       )
--       · simp
--         have : (∅: Finset (A ⊕ B)).toLeft = ∅ := by ext x; simp
--         have : (∅: Finset (A ⊕ B)).toRight = ∅ := by ext x; simp
--         aesop
--       · intro a s has ih
--         simp [has]
--         match a with
--         | Sum.inl a1 => simp [has, ih]; group
--         | Sum.inr b1 => simp [has, ih]; group; apply congr; rw [mul_comm]; rfl

theorem AlgebraicIndependent.transcendental_extends {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (x : Set A) {s : Set A}
  (h1 : AlgebraicIndependent R (Subtype.val : x → A))
  (h2 : s ⊆ x)
  {a : A}
  (ha1 : a ∈ (x \ s))
  : Transcendental (Algebra.adjoin R s) a := by
    rw [show s = Set.range (Subtype.val : s → A)
        by simp only [Subtype.range_coe_subtype,
        Set.setOf_mem_eq]]
    rw [<-option_iff]
    rw [<-algebraicIndependent_subtype_range]
    · apply mono ?_ h1
      rw [Set.range_subset_iff]
      intro y
      match y with
      | Option.some s => aesop
      | Option.none => aesop
    · intro x y hxy
      match x, y with
      | Option.some x, Option.some y => aesop
      | Option.none, Option.none => aesop
      | Option.some x, Option.none => aesop
      | Option.none, Option.some y => aesop
    · exact mono h2 h1

theorem IsTranscendenceBasis.iff_isAlgebraic {R A I : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial R] {s : I -> A} (h : AlgebraicIndependent R s) :
  IsTranscendenceBasis R s <-> Algebra.IsAlgebraic (Algebra.adjoin R (Set.range s)) A := by
    constructor
    · exact fun a ↦ isAlgebraic a
    · intro h1
      constructor
      · exact h
      · intro s1 hs1 hs2
        apply le_antisymm hs2
        by_contra hs21
        simp [Set.not_subset] at hs21
        let ⟨a, ha⟩ := hs21
        have := h1.isAlgebraic a
        have := AlgebraicIndependent.transcendental_extends (x := s1) (s := Set.range s) hs1 hs2 (a := a) (by aesop)
        contradiction

instance algebra_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]  {s : Set L} :
  Algebra (Algebra.adjoin K s) (IntermediateField.adjoin K s) := RingHom.toAlgebra (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K s))

lemma adjoin_on_algebra_adjoin_eq_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]  {s : Set L} :
  IntermediateField.adjoin K (Algebra.adjoin K s) = IntermediateField.adjoin K s := by
    apply le_antisymm
    · have := IntermediateField.adjoin.mono K _ _ (SetLike.coe_subset_coe.mpr (IntermediateField.algebra_adjoin_le_adjoin K s))
      simp only [IntermediateField.coe_toSubalgebra, IntermediateField.adjoin_self] at this
      exact this
    · apply IntermediateField.adjoin.mono
      exact Algebra.subset_adjoin

lemma Subalgebra.inclusion_range_subtype_val {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {S T : Subalgebra R A} (h : S ≤ T) :
  Subtype.val '' (Set.range (Subalgebra.inclusion h)) = S := by
    aesop

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 400000
instance {K L : Type*} [Field K] [Field L] [Algebra K L]  {s : Set L} :
  IsFractionRing (Algebra.adjoin K s) (IntermediateField.adjoin K s) := by
    -- it's easy in math that K(s) is the fraction field of K[s]
    let inclusion := Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K s)
    let inclusion_injective : Function.Injective inclusion := Subalgebra.inclusion_injective (IntermediateField.algebra_adjoin_le_adjoin K s)
    -- manually write these instances because time out
    letI : Module (Algebra.adjoin K s) (IntermediateField.adjoin K s) := Algebra.toModule
    letI : NoZeroSMulDivisors (Algebra.adjoin K s) (IntermediateField.adjoin K s) := NoZeroSMulDivisors.iff_algebraMap_injective.mpr inclusion_injective

    letI := FractionRing.liftAlgebra (Algebra.adjoin K s) (IntermediateField.adjoin K s)

    -- we use the fact that, the canolical lift map of inclusion can be proved to be bijective, hence the fraction field of K[s] is isomorphic to K(s)
    let lift_inclusion : (FractionRing (Algebra.adjoin K s)) →ₐ[K] (IntermediateField.adjoin K s) := IsFractionRing.liftAlgHom inclusion_injective
    let lift_inclusion_equiv := AlgEquiv.ofBijective lift_inclusion (
      by
        constructor
        · unfold lift_inclusion IsFractionRing.liftAlgHom
          simp only [IsLocalization.coe_liftAlgHom, AlgHom.toRingHom_eq_coe]
          rw [IsLocalization.lift_injective_iff]
          unfold inclusion
          intro x y
          constructor
          intro a
          simp_all only [IsFractionRing.coe_inj, RingHom.coe_coe]
          intro h
          -- don't know why rw [`Subalgebra.coe_toRingHom`] doesn't work
          have : inclusion x = inclusion y := by
            unfold inclusion
            exact h
          aesop
        · rw [<-Set.range_eq_univ]
          unfold lift_inclusion
          rw [<-AlgHom.coe_fieldRange]
          rw [IsFractionRing.liftAlgHom_fieldRange]
          · unfold inclusion
            simp only [AlgHom.coe_range]
            rw [<-IntermediateField.coe_top (F := K)]
            rw [SetLike.coe_set_eq]
            apply_fun IntermediateField.lift (L := L) <;> simp only [IntermediateField.lift_adjoin,
              IntermediateField.lift_top, IntermediateField.lift_injective]
            simp_rw [<-adjoin_on_algebra_adjoin_eq_adjoin (s := s)]
            apply congrArg
            exact Subalgebra.inclusion_range_subtype_val _
    )
    rw [IsFractionRing]
    let lift_inclusion_equiv' : (FractionRing (Algebra.adjoin K s)) ≃ₐ[(Algebra.adjoin K s)] (IntermediateField.adjoin K s) := AlgEquiv.ofRingEquiv (f := lift_inclusion_equiv) (by
      intro x
      aesop
    )
    have := IsLocalization.isLocalization_iff_of_algEquiv ((nonZeroDivisors (Algebra.adjoin K s)) ) lift_inclusion_equiv'.symm (R := (Algebra.adjoin K s))
    rw [this]
    exact Localization.isLocalization



theorem IsAlgebraic.on_algebra_adjoin_iff_on_field_adjoin {R A : Type*} [Field R] [Field A] [Algebra R A] [Nontrivial R] {s : Set A} :
  Algebra.IsAlgebraic (Algebra.adjoin R s) A ↔ Algebra.IsAlgebraic (IntermediateField.adjoin R s) A := by
      haveI : IsScalarTower ((Algebra.adjoin R s)) ((IntermediateField.adjoin R s)) A
       := IsScalarTower.of_algebraMap_smul fun r ↦ congrFun rfl
      -- wu use the fact that if K is the fraction field of A, then C is algebraic on A iff C is algebraic on K
      rw [IsFractionRing.comap_isAlgebraic_iff (K := (IntermediateField.adjoin R s))]

def IntermediateField.restrictScalars_algEquiv.{u_1, u_2, u_3} {K : Type u_1} {L : Type u_2} {L' : Type u_3} [Field K] [Field L]
  [Field L'] [Algebra K L] [Algebra K L'] [Algebra L' L] [IsScalarTower K L' L] {E : IntermediateField L' L} :
  E ≃ₐ[K] IntermediateField.restrictScalars K E := AlgEquiv.refl

instance Algebra.ofIntermediateFieldAdjoin {F K E : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] (T : IntermediateField F K) (t : Set E) :
  Algebra (IntermediateField.adjoin T t) (IntermediateField.adjoin K t) := RingHom.toAlgebra (
    let adKt1 : (IntermediateField (↥T) E) := IntermediateField.restrictScalars _ (IntermediateField.adjoin K t)
    let algHom1 := IntermediateField.inclusion (E := (IntermediateField.adjoin T t)) (F := adKt1) (by
      unfold adKt1
      simp
      exact IntermediateField.subset_adjoin K t
    )
    ((IntermediateField.restrictScalars_algEquiv).symm.toAlgHom.comp algHom1)
  )


-- not an instance because timeout
theorem IsAlgebraic.to_intermediateField_adjoin {F K E : Type*} [Field F] [Field K] [Field E] [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E] {T : IntermediateField F K} {t : Set E} [Algebra.IsAlgebraic T K] :
  Algebra.IsAlgebraic (IntermediateField.adjoin T t) (IntermediateField.adjoin K t) := by
    -- Take the algebraic closure in (IntermediateField.adjoin K t), it' s easy to show it is a field and contains K, t
    let closure := integralClosure (IntermediateField.adjoin T t) E
    let closure1 := Subalgebra.toIntermediateField' closure (by
      apply IsIntegralClosure.isField (R := IntermediateField.adjoin T t) (B := E) closure
      exact Semifield.toIsField (IntermediateField.adjoin T t)
      )
    have K_subset1 : (Set.range (algebraMap K E) : Set E) ⊆ (closure : Set _) := by
      rw [Set.range_subset_iff]
      intro k
      unfold closure
      simp
      rw [mem_integralClosure_iff]
      rw [<-isAlgebraic_iff_isIntegral]
      apply IsAlgebraic.tower_top (K := T)
      rw [isAlgebraic_ringHom_iff_of_comp_eq (f := RingEquiv.refl T) (g := algebraMap K E)]
      · exact Algebra.IsAlgebraic.isAlgebraic k
      · exact NoZeroSMulDivisors.algebraMap_injective K E
      · exact rfl
    have t_subset : t ⊆ (closure : Set _) := by
      unfold closure
      apply subset_trans ?_ (Subalgebra.range_subset _)
      -- rw [<-IntermediateField.coe_bot]
      apply subset_trans (IntermediateField.subset_adjoin T t)
      apply subset_of_eq
      aesop
    have adjoin_subset : (IntermediateField.adjoin K t : Set E) ⊆ closure := by
      -- can't find lemmas to prove it, so we have to use the definition
      unfold IntermediateField.adjoin
      simp
      show (Subfield.closure (Set.range (algebraMap K E) ∪ t) : Set E) ⊆ closure1.toSubfield
      rw [SetLike.coe_subset_coe]
      aesop
    rw [Algebra.isAlgebraic_iff_isIntegral]
    rw [Algebra.isIntegral_def]
    intro ⟨e, he⟩
    letI : IsScalarTower (IntermediateField.adjoin T t) (IntermediateField.adjoin K t) E := by
      apply IsScalarTower.of_algebraMap_smul
      aesop
    rw [<-isIntegral_algebraMap_iff (B := E)]
    aesop
    exact NoZeroSMulDivisors.algebraMap_injective (↥(IntermediateField.adjoin K t)) E


theorem union_of_basis_is_basis
    {F K E : Type*}
    [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E]
    [IsScalarTower F K E]
    {I1 I2 : Type*}
    [DecidableEq I1] [DecidableEq I2]
    (s : I1 -> K) (t : I2 -> E)
    (hs : IsTranscendenceBasis F s)
    (ht : IsTranscendenceBasis K t) :
    let basis_union := Sum.elim t ((algebraMap K E) ∘ s)
    IsTranscendenceBasis F basis_union := by
  extract_lets basis_union
  -- verify the definition, i.e. algebraic independent and E is algebraic over F
  apply (IsTranscendenceBasis.iff_isAlgebraic ?_).mpr
  pick_goal 2
  ·
    -- to show the union is algebraic independent, suppose we have a polynomial $p$ such that $p(s, t) = 0$, hence $p(s, x)$ is a polynomial in which $s$ eval to $0$. By algebraic independence of $s$, we have $p(s, x) = 0$ for all $x$. Notice that every coeffient of $p(s, x)$ is a evaluation on $s$ of a polynomial in E, hence $p(s, x) = 0$ implies every coeffient is zero, hence $p = 0$.
    have hs1 := hs.1
    have ht1 := ht.1
    rw [algebraicIndependent_iff] at ht1 ⊢
    simp [basis_union]
    intro p hp
    rw [MvPolynomial.aeval_sum_elim] at hp
    apply ht1 at hp
    let sum_equiv := MvPolynomial.sumAlgEquiv F I2 I1
    generalize h: MvPolynomial.sumAlgEquiv F I2 I1 p = p1
    have : p = sum_equiv.symm p1 := by
      rw [<-h]
      unfold sum_equiv
      rw [AlgEquiv.symm_apply_apply]
    simp_rw [this] at hp ⊢
    -- because theorem give us a strange form, we must manually prove that every coeff is again a eval of some polynomial
    have (p : MvPolynomial I2 (MvPolynomial I1 F)) : (MvPolynomial.aeval (Sum.elim MvPolynomial.X (MvPolynomial.C ∘ s))) (MvPolynomial.iterToSum F I2 I1 p) =  MvPolynomial.map (MvPolynomial.aeval s (R := F)) p := by
      apply MvPolynomial.induction_on p
      · simp [MvPolynomial.aeval_rename]
        intro a
        rfl
      · intro p q hp hq
        -- strangely can't find the instance unless manually specify f
        repeat rw [map_add (f := MvPolynomial.iterToSum F I2 I1)]
        simp [hp, hq]
      · intro p n hp
        rw [map_mul (f := MvPolynomial.iterToSum F I2 I1)]
        simp [hp]
    unfold sum_equiv at hp
    simp at hp
    rw [this] at hp
    simp
    -- under this form, we can use the injective property comes from algebraicIndependent of sapply_fun MvPolynomial.map (MvPolynomial.aeval s (R := F))
    rw [map_eq_zero_iff] at hp
    · exact hp
    · apply MvPolynomial.map_injective
      exact hs1
  ·
    -- pay attention that the definition of basis in mathlib is $K$ is algebraic on $F[t]$, rather than on $F(s)$ which the stack project uses, but they are equivalent.
    -- to show $E$ is algebraic over $F(s, t)$, just use the transitivity of algebraic extension and $K$ is algebraic over $F(s)$, hence $K(t)$ is algebraic over $F(t, s)$, hence $E$ is algebraic over $F(t, s)$.
    apply IsTranscendenceBasis.isAlgebraic at hs
    apply IsTranscendenceBasis.isAlgebraic at ht
    rw [IsAlgebraic.on_algebra_adjoin_iff_on_field_adjoin] at *
    -- rw [Algebra.isAlgebraic_def]
    -- intro x
    have : Set.range basis_union = (Set.range t) ∪ ((algebraMap K E) '' (Set.range s)) := by
      unfold basis_union
      aesop
    rw [this]
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin (IntermediateField.adjoin F (Set.range s)) (Set.range t)) (IntermediateField.adjoin K (Set.range t)) := IsAlgebraic.to_intermediateField_adjoin
    rw [<-IntermediateField.adjoin_adjoin_left, IntermediateField.adjoin_adjoin_comm, <-IsScalarTower.coe_toAlgHom' F K E, <-IntermediateField.adjoin_map]
    rw [IntermediateField.restrictScalars_adjoin_of_algEquiv (IntermediateField.equivMap ((IntermediateField.adjoin F (Set.range s))) ((IsScalarTower.toAlgHom F K E))).symm]
    letI alg_ins : Algebra (IntermediateField.restrictScalars F
        (IntermediateField.adjoin ((IntermediateField.adjoin F (Set.range s))) (Set.range t))) (IntermediateField.adjoin K (Set.range t)) := RingHom.toAlgebra  (by
      apply RingHom.comp ?_ IntermediateField.restrictScalars_algEquiv.symm.toRingHom
      apply algebraMap
      -- ext x
      -- simp
      -- generalize h : ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E)).symm x = y
      -- have : x = ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E)) y := by
      --   rw [<-h]
      --   exact
      --     Eq.symm
      --       (AlgEquiv.apply_symm_apply
      --         ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E))
      --         x)
      -- rw [this]
      -- rfl
    )
    letI scalar_tower : IsScalarTower (IntermediateField.restrictScalars F
        (IntermediateField.adjoin ((IntermediateField.adjoin F (Set.range s))) (Set.range t))) (IntermediateField.adjoin K (Set.range t)) E := by
      apply IsScalarTower.of_algebraMap_eq
      exact fun _ => rfl
    apply Algebra.IsAlgebraic.trans (L := (IntermediateField.adjoin K (Set.range t))) (L_alg := ?_)
    apply Algebra.IsAlgebraic.of_ringHom_of_comp_eq (f := (IntermediateField.restrictScalars_algEquiv (K := F)).symm) (g := RingHom.id _)
    -- remaining goals are boring
    · exact AlgEquiv.surjective IntermediateField.restrictScalars_algEquiv.symm
    · exact fun ⦃a₁ a₂⦄ a ↦ a
    · ext x
      simp
      generalize h : IntermediateField.restrictScalars_algEquiv.symm x = y
      have : x = IntermediateField.restrictScalars_algEquiv y := by
        rw [<-h]
        exact Eq.symm (AlgEquiv.apply_symm_apply IntermediateField.restrictScalars_algEquiv x)
      rw [this]
      rfl
    · ext x
      simp
      generalize h : ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E)).symm x = y
      have : x = ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E)) y := by
        rw [<-h]
        exact
          Eq.symm
            (AlgEquiv.apply_symm_apply
              ((IntermediateField.adjoin F (Set.range s)).equivMap (IsScalarTower.toAlgHom F K E))
              x)
      rw [this]
      rfl
