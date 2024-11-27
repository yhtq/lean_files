import Mathlib

theorem Finset.prod_sum_type {A B C : Type*} [DecidableEq A] [DecidableEq B] [CommMonoid C] {s: Finset (A ⊕ B)} {f : (A ⊕ B) -> C} :
  s.prod f =
    (s.toLeft.prod (f ∘ Sum.inl)) * (s.toRight.prod (f ∘ Sum.inr)) := by
      apply Finset.induction (
        p := fun s => s.prod f = (s.toLeft.prod (f ∘ Sum.inl)) * (s.toRight.prod (f ∘ Sum.inr))
      )
      · simp
        have : (∅: Finset (A ⊕ B)).toLeft = ∅ := by ext x; simp
        have : (∅: Finset (A ⊕ B)).toRight = ∅ := by ext x; simp
        aesop
      · intro a s has ih
        simp [has]
        match a with
        | Sum.inl a1 => simp [has, ih]; group
        | Sum.inr b1 => simp [has, ih]; group; apply congr; rw [mul_comm]; rfl
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
  -- verify the definition
  constructor
  ·
    have hs1 := hs.1
    have ht1 := ht.1
    rw [algebraicIndependent_iff] at *
    simp [basis_union]
    intro p hp
    rw [MvPolynomial.aeval_sum_elim] at hp
    apply ht1 at hp
    simp [MvPolynomial.ext_iff] at hp
    simp [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq, MvPolynomial.coeff_sum] at hp
    simp [Finset.prod_sum_type] at hp
    -- apply MvPolynomial.ext
    -- simp
    -- intro m
    -- rw [MvPolynomial.aeval_def] at hp

    -- rw [show
    --   (MvPolynomial.C : K →+* MvPolynomial I2 K) = algebraMap K (MvPolynomial I2 K) from rfl] at hp
    -- rw [MvPolynomial.aeval_sum_elim] at hp
#check MvPolynomial.ext_iff
#leansearch "Finset.prod_sum_type?"
#leansearch "Finset.toLeft?"
