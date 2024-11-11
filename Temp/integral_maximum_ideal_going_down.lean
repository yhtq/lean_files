import Mathlib
-- 1. Consider the injection $i: A \rightarrow B$, then $P = i^{-1} (Q)$ which is obviously a prime ideal as well as canonical injection $A / P \rightarrow B / Q$
-- 2. Obviously $B / Q$ is integral on A, and there is a canonical surjective map $\pi$, which deduces null polynomial of $x$ is of course a null polynomial of  $\pi (x)$
-- 3. It's enough to show $B / Q \text{ is field if and only if } A / P \text{ if field}$, which comes from the fact if one integral domain is integral on another, then they are both field or both not.

open Ideal

variable
    {A B: Type*} [CommRing A] [CommRing B] [Algebra A B] [Nontrivial B]
    [Algebra.IsIntegral A B]
    (inj: Function.Injective (algebraMap A B))
    (Q: Ideal B) [IsPrime Q]
-- manually define to have better defEq
abbrev P : Ideal A := Ideal.comap (algebraMap A B) Q

-- comap of prime ideal is prime, which is a theorem in mathlib
instance : IsPrime (P Q (A := A)) := inferInstance

-- actually it can be proved by infer_instance, but we here manually prove
theorem quotient_integral: Algebra.IsIntegral (A ⧸ ((P Q (A := A)))) (B ⧸ Q) := by
  haveI : Algebra.IsIntegral A (B ⧸ Q) := inferInstance
  have quotient_integral_B: Algebra.IsIntegral (A ⧸ ((P Q (A := A)))) B := inferInstance
