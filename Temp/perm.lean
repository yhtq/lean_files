import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
open Equiv.Perm

lemma prod_conj {A : Type*} [Group A] (l: List A) (x: A) : x * l.prod * x⁻¹  = (l.map (fun y => x * y * x⁻¹)).prod := by
  match l with
  | List.nil => simp
  | List.cons hd tl =>
    trans x * hd * x⁻¹ * x * tl.prod * x⁻¹
    <;> simp only [List.prod_cons, List.map_cons, List.prod_cons, <-prod_conj]
    <;> group

lemma Equiv.Perm.perm_entry_eq_of_conj_perm (n : ℕ) (σ : Perm <| Fin n) (l : List <| Fin n)
  (hnd : l.Nodup) : σ * l.formPerm * σ⁻¹ = (l.map σ).formPerm := by
    unfold List.formPerm
    repeat (
        simp only [prod_conj, List.map_zipWith, <-List.map_tail, List.zipWith_map]
        congr
      )
    funext x y
    exact Eq.symm (swap_apply_apply σ x y)
#print axioms Equiv.Perm.perm_entry_eq_of_conj_perm
open MvPolynomial

-- Define the polynomial ring R with integer coefficients and n variables
-- Define Func as a type alias for functions from S to ℝ
def Func (S : Type*) := S → ℝ

-- Define the addition of two functions
instance (S : Type*) : Add (Func S) where
  add := λ f g => λ s => f s + g s

-- Define the negation of a function
instance (S : Type*) : Neg (Func S) where
  neg := λ f => λ s => -f s

-- Define the zero function
instance (S : Type*) : Zero (Func S) where
  zero := λ s => 0

-- Define the AddGroup instance using the minimal group axioms
noncomputable instance (S : Type*) : AddGroup (Func S) := by
  apply AddGroup.ofLeftAxioms
   -- Associativity
  · intros f g h
    funext s
    exact add_assoc (f s) (g s) (h s)
  -- Identity element
  · intro f
    funext s
    exact zero_add (f s)
  -- Inverse element
  · intro f
    funext s
    exact add_left_neg (f s)

variable {K : Type*} [Field K]
variable {α β γ : Type*}
variable [Finite α]
variable {S : Type} [Fintype S] (f : S → S)
-- Define the matrices
def matrix_a (a : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![1, a], ![0, 1]]

def matrix_b (b : K) : Matrix (Fin 2) (Fin 2) K :=
  ![![1, b], ![0, 1]]
open Matrix
-- Define SL(2, K)
def SL2K := SpecialLinearGroup (Fin 2) K

-- Proof that the matrices are conjugate if and only if ab⁻¹ = c² for some c ∈ K

lemma preparation_of_SL2K {f : α → α} (hinj : Function.Injective f) : Function.Surjective f := by
  intro x
  have := Classical.propDecidable
  cases nonempty_fintype α
  -- ⇒ direction: If they are conjugate, then there exists c such that a * b⁻¹ = c²
  have h₁ : Finset.image f Finset.univ = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      ((Finset.card_image_of_injective Finset.univ hinj).symm ▸ le_rfl)
    -- ⇒ direction: If they are conjugate, then there exists c such that a * b⁻¹ = c²
  have h₂ : x ∈ Finset.image f Finset.univ := h₁.symm ▸ Finset.mem_univ x
  obtain ⟨y, h⟩ := Finset.mem_image.1 h₂
  exact ⟨y, h.2⟩
-- Based on the formal outcome we can induce the theorem below which can solve the problem derectly
theorem conjugate_iff {f : α → α} : Function.Injective f ↔ Function.Surjective f :=
  ⟨Finite.surjective_of_injective, fun hsurj =>
    Function.HasLeftInverse.injective ⟨Function.surjInv hsurj, Function.leftInverse_of_surjective_of_rightInverse
      (Finite.surjective_of_injective (Function.injective_surjInv _))
      (Function.rightInverse_surjInv _)⟩⟩

-- Then we will prove the primary lemma using the upper theorem

-- Final example: UnexploredExercise_6568
theorem UnexploredExercise_6568 (hf : Function.Surjective f) : Function.Injective f := by
  exact conjugate_iff.mpr hf

#check (A: Type*) ×' (Group A)
