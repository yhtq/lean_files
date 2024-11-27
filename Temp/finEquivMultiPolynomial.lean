import Mathlib
namespace MvPolynomial
#check Nat

@[reducible]
noncomputable def nthPolynomial.{u} (R : Type u) [CommSemiring R] (n : ℕ) : (T : Type u) × (CommSemiring T) :=
  match n with
  | 0 => ⟨R, inferInstance⟩
  | Nat.succ m =>
    letI commSemiring := (nthPolynomial R m).2
    ⟨Polynomial ((nthPolynomial R m).1), inferInstance⟩
termination_by n


noncomputable instance {R : Type*} [CommSemiring R] (n : ℕ) : CommSemiring (nthPolynomial R n).1 :=
  (nthPolynomial R n).2

noncomputable instance alg_instance {R : Type*} [CommSemiring R] (n : ℕ) : Algebra R (nthPolynomial R n).1 :=
  match n with
  | 0 => by show Algebra R R; infer_instance
  | Nat.succ m =>
    letI commSemiring := (nthPolynomial R m).2
    letI algebra := alg_instance  m (R := R)
    by show Algebra R (Polynomial ((nthPolynomial R m).1)); infer_instance

@[reducible]
noncomputable def nthPolynomialEval {R : Type*} [CommSemiring R] (n : ℕ) (σ : Fin n -> R) : (nthPolynomial R n).1 →+* R :=
  match n with
  | 0 => RingHom.id R
  | Nat.succ m =>
    let eval := nthPolynomialEval m
    fun p => Polynomial.eval (fun i => eval (Polynomial.coeff p i)) p

noncomputable def finEquiv (R : Type*) [CommSemiring R] (n : ℕ) : (MvPolynomial (Fin n) R) ≃ₐ[R] (nthPolynomial R n).1 :=
  match n with
  | 0 => isEmptyAlgEquiv R (Fin 0)
  | Nat.succ m =>
    let equiv1 := finSuccEquiv R m
    let equiv2 := finEquiv R m
    by
      show (MvPolynomial (Fin (Nat.succ m)) R) ≃ₐ[R] Polynomial (nthPolynomial R m).1
      exact equiv1.trans (Polynomial.mapAlgEquiv equiv2)

noncomputable def finEquiv_zero {R : Type*} [CommSemiring R] : (MvPolynomial (Fin 0) R) ≃ₐ[R] R := finEquiv R 0
noncomputable def finEquiv_one {R : Type*} [CommSemiring R] : (MvPolynomial (Fin 1) R) ≃ₐ[R] Polynomial R := finEquiv R 1
noncomputable def finEquiv_two {R : Type*} [CommSemiring R] : (MvPolynomial (Fin 2) R) ≃ₐ[R] Polynomial (Polynomial R) := finEquiv R 2
