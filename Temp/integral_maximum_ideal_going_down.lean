import Mathlib
-- 1. Consider the injection $i: A \rightarrow B$, then $P = i^{-1} (Q)$ which is obviously a prime ideal as well as canonical injection $A / P \rightarrow B / Q$
-- 2. Obviously $B / Q$ is integral on A, and there is a canonical surjective map $\pi$, which deduces null polynomial of $x$ is of course a null polynomial of  $\pi (x)$
-- 3. Notice that actuall $A / Q$ is a sub integral domain of $B / P$ (it' s easy to prove the quotient map is injective). It's enough to show $B / Q \text{ is field if and only if } A / P \text{ if field}$, which comes from the fact if one integral domain is integral on another, then they are both field or both not.

open Ideal

variable
    {A B: Type*} [CommRing A] [CommRing B] [Algebra A B] [Nontrivial B]
    [Algebra.IsIntegral A B]
    (_: Function.Injective (algebraMap A B))  -- in fact, this condition is not necessary
    (Q: Ideal B) [IsPrime Q]
-- manually define to have better defEq
abbrev P_aux : Ideal A := Ideal.comap (algebraMap A B) Q

-- comap of prime ideal is prime, which is a theorem in mathlib
instance : IsPrime (P_aux Q (A := A)) := inferInstance

-- the Algebra (A / P) (B / Q) is injective, means (A / P) can be seen as a subring of (B / Q)
instance : NoZeroSMulDivisors (A ⧸ ((P_aux Q (A := A)))) (B ⧸ Q) := inferInstance

-- actually it can be proved by infer_instance, but we here manually prove
theorem quotient_integral: Algebra.IsIntegral (A ⧸ ((P_aux Q (A := A)))) (B ⧸ Q) := by
  haveI : Algebra.IsIntegral A (B ⧸ Q) := inferInstance
  rw [Algebra.isIntegral_def] -- to show every element is integral
  intro b'
  have : IsIntegral A b' := Algebra.IsIntegral.isIntegral b'  -- b' is integral over A
  simp [IsIntegral, RingHom.IsIntegralElem] at this ⊢ -- use the definition of integral element
  let ⟨p, ⟨hp1, hp2⟩⟩ := this
  use Polynomial.map (Ideal.Quotient.mk (P_aux Q (A := A))) p -- map this polynomial to A / P
  constructor
  · exact Polynomial.Monic.map (Ideal.Quotient.mk (P_aux Q)) hp1
  · rw [Polynomial.eval₂_map]
    rw [show (Ideal.Quotient.mk (P_aux Q (A := A))) = algebraMap A (A ⧸ P_aux Q) from rfl]  -- to use the commutativity of quotient map, we must rewrite it to algebraMap form
    rw [<-IsScalarTower.algebraMap_eq]
    exact hp2

theorem ifField_iff : Ideal.IsMaximal Q ↔ Ideal.IsMaximal  (P_aux Q  (A := A)) := by
  -- quotient ring is field iff ideal is maximal
  repeat rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  haveI : Algebra.IsIntegral (A ⧸ P_aux Q) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ P_aux Q) := inferInstance
  haveI : IsDomain (B ⧸ Q) := inferInstance
  apply Iff.symm
  -- use the fact that if one integral domain is integral on another, then they are both field or both not
  apply Algebra.IsIntegral.isField_iff_isField
  -- the quotient map is obviously injective
  exact algebraMap_quotient_injective
