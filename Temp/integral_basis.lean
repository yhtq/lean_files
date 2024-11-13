import Mathlib
#check NumberField.integralBasis
-- Just use the fact that, if $\alpha_{i}$ is
noncomputable def to_basis_on_ℚ
    {I K: Type*} [Field K] [NumberField K]
    (basis: Basis I ℤ  (NumberField.RingOfIntegers K)):
    Basis I ℚ K := by
      -- the basis map comes from composition of the algebra map and the basis map from I to (NumberField.RingOfIntegers K)
      apply Basis.mk (v := (algebraMap (NumberField.RingOfIntegers K) K) ∘ basis)
      ·
        -- linear indenpent infer linear indenpent on localisation
        apply LinearIndependent.localization_localization (R := ℤ) (S := nonZeroDivisors ℤ) (Rₛ := ℚ)
        exact Basis.linearIndependent basis
      ·
        -- is a generator infer is a generator on localisation
        apply ge_of_eq
        rw [Set.range_comp]
        apply span_eq_top_localization_localization (R := ℤ) (S := nonZeroDivisors ℤ) (Rₛ := ℚ)
        exact Basis.span_eq basis


#leansearch "Submodule.span localization?"
#leansearch "equal infer ge?"
#leansearch "Set.range (f ∘ g) = f '' Set.range g?"
