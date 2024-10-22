import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.FieldTheory.Finite.GaloisField
import Init.Data.Nat.Basic
import Mathlib.Algebra.Ring.Defs
open Polynomial List Nat


open Pointwise

def Group.product_equiv_of_disjoint {G : Type*} [Group G] (H K : Subgroup G) (h : H.carrier ∩ K.carrier = {1}) : (H * K : Set G) ≃ H × K := sorry

noncomputable def construct_polynomial_from_list {R : Type*} [Nontrivial R] [Semiring R] (l : List R): Polynomial R :=
  match l with
  | [] => 0
  | hd :: tl => C hd + X * construct_polynomial_from_list tl


def polynomial_from_list {R : Type*} [Nontrivial R] [Semiring R] (l : List R)(non_empty : l ≠ [])(non_zero : getLast l non_empty ≠ 0) : ∃ p: Polynomial R, natDegree p = l.length - 1 ∧ (∀ n: Fin l.length, p.coeff n = l.get n) := by
  induction l with
  | nil =>
      exfalso
      contradiction
  | cons hd tl ih =>
    cases tl with
    | nil =>
      use C hd
      simp
    | cons hd' tl'  =>
      have this1: (hd' :: tl') ≠ [] := by
        simp
      have this2: (hd' :: tl').getLast (by simp) ≠ 0 := by
       simp at non_zero
       simp
       exact non_zero
      let ⟨high_part, h1, h2⟩ := ih this1 this2
      have high_part_non_zero : high_part ≠ 0 := by
        by_cases h: tl' = []
        · have hd'_non_zero : hd' ≠ 0 := by
            have : (hd :: hd' :: tl').getLast non_empty = hd'  := by
              have : (hd :: hd' :: tl').getLast non_empty = (hd :: hd' :: []).getLast (by simp) := by
                exact
                  getLast_congr non_empty
                    (of_eq_true
                      (Eq.trans (congrArg Not (eq_false' fun h ↦ List.noConfusion h))
                        not_false_eq_true))
                    (congrArg (cons hd) (congrArg (cons hd') h))
              rw [this]
              simp
            rw [<-this]
            exact non_zero
          have p1:high_part.coeff 0 = hd' := by
            apply h2 ⟨0, by simp only [length_cons, succ_eq_add_one, lt_add_iff_pos_left,
              add_pos_iff, zero_lt_one, or_true]⟩
          by_contra a
          have : high_part.coeff 0 = 0 := by
            exact Mathlib.Tactic.ComputeDegree.coeff_congr (congrFun (congrArg coeff a) 0) rfl rfl
          rw [<-p1] at hd'_non_zero
          exact hd'_non_zero this




        · refine zero_le_degree_iff.mp ?_
          have p1: high_part.natDegree > 0 := by
            rw [h1]
            simp
            exact length_pos.mpr h
          have : high_part.degree = high_part.natDegree := by
            exact (degree_eq_iff_natDegree_eq_of_pos p1).mpr rfl
          rw [this]
          exact Nat.WithBot.coe_nonneg
      let n := tl'.length + 1
      use C hd + X * high_part
      have : (hd :: hd' :: tl').length - 1 = n := by
        simp
      rw [this]
      have : n = natDegree high_part + 1 := by
        rw [h1]
        eq_refl
      apply And.intro
      · simp
        rw [this]
        let t := natDegree_X_mul high_part_non_zero
        rw [t]
      · intro i
        have non_zero1: (hd :: hd' :: tl').length > 0 := by
          exact length_pos.mpr non_empty
        by_cases h: i = ⟨ 0, non_zero1 ⟩
        ·
          rw [h]
          simp
        · simp
          have i_non_zero : i.val ≠ 0 := by
            by_contra h'
            have : i = ⟨0, non_zero1⟩  := by
              have : (⟨0, non_zero1⟩ :  Fin (hd :: hd' :: tl').length).val = 0 := by
                rfl
              rw [<-this] at h'
              apply Fin.eq_of_val_eq h'
            tauto
          have : (C hd).coeff ↑i = 0 := by
            rw [coeff_C]
            simp
            intro h'
            exfalso
            have : (0 : ℕ )= ↑(⟨0, non_zero1⟩ :  Fin (hd :: hd' :: tl').length) := by
              rfl
            rw [this] at h'
            let temp := Fin.eq_of_val_eq h'
            tauto
          rw [this]
          simp only [zero_add]
          let pre_i := Fin.pred i h
          let t := Fin.coe_pred i h
          have : i.val = pre_i.val + 1 := by
            rw [t]
            simp
            have : i.val - 1 + 1 = i.val := by
               apply Nat.sub_add_cancel
               exact one_le_iff_ne_zero.mpr i_non_zero
            rw [this]
          rw [this]
          rw [coeff_X_mul]
          have : (hd :: hd' :: tl').get i = (hd' :: tl').get (pre_i) := by
            have : i = pre_i.succ := by
              exact Eq.symm (Fin.succ_pred i h)
            rw [this]
            exact rfl
          rw [this]
          exact h2 pre_i







          -- have : (C hd).coeff ↑i = hd := by
          --   rw [coeff_C]
          --   rw [h]
          --   simp
          -- rw [this]
          -- have : (X * high_part).coeff ↑i = 0 := by
          --   rw [h]
          --   apply coeff_X_mul_zero
          -- rw [this]
          -- simp
def temp : ([1, 1, 1] : List ℤ) = ([1, 2-1, 1] : List ℤ) :=
  by
    congr

#help tactic


structure PolynomialList (R: Type)  [DecidableEq R] [Nontrivial R] [CommRing R]  where
  mk ::
  coeffs : List R
  non_zero : (p : coeffs  ≠ []) -> coeffs.getLast p ≠ 0

#check Subtype.ext

variable {R: Type} [DecidableEq R] [Nontrivial R] [CommRing R]
theorem polynomial_congr {p1 p2 : PolynomialList R}  : p1 = p2 := sorry
def drop_trailing_zeros  (l : List R) : List R :=
  reverse $ dropWhile (fun x => x == 0) (reverse l)
def valid_coeff (l: List R) := (p: l ≠ []) → l.getLast p ≠ 0

theorem get_zero_eq_head (l: List R) {non_empty : l ≠ []} {lt_zero : l.length > 0} : l.get ⟨0, lt_zero⟩ = l.head non_empty := by
  cases l with
  | nil =>
    exfalso
    contradiction
  | cons hd tl =>
    rfl
theorem drop_trailing_zeros_last_non_zero  (l : List R) : valid_coeff (drop_trailing_zeros l) :=
  by
    unfold valid_coeff
    intro p
    unfold drop_trailing_zeros at p
    unfold drop_trailing_zeros
    rw [getLast_reverse p]
    let lemma1(l' : List R)(p': dropWhile (fun x => x == 0) l' ≠ []) : head (dropWhile (fun x => x == 0) l') p' ≠ 0 := by
      induction l' with
      | nil => rw [dropWhile_nil] at p'; contradiction
      | cons hd tl tail_ih =>
        by_cases h: hd = 0
        · have : dropWhile (fun x ↦ x == 0) (hd :: tl) = dropWhile (fun x ↦ x == 0) tl := by
            rw [dropWhile_cons]
            simp
            intro h'
            contradiction
          let p'' := p'
          rw [this] at p''
          have : (dropWhile (fun x ↦ x == 0) (hd :: tl)).head p' = (dropWhile (fun x ↦ x == 0) tl).head p'' := by
            congr
          rw [this]
          let tlr := tl.reverse
          have : drop_trailing_zeros tlr ≠ [] := by
            unfold drop_trailing_zeros
            by_contra h'
            apply reverse_eq_nil_iff.mp at h'
            rw [reverse_reverse tl] at h'
            contradiction

          let rp := tail_ih p''
          exact rp
        · have non_zero : (hd == 0) = False := by
            simp only [beq_iff_eq, eq_iff_iff, iff_false]
            exact h
          have : dropWhile (fun x ↦ x == 0) (hd :: tl) = hd :: tl := by
            rw [dropWhile_cons]
            simp only [non_zero]
            simp
          have : (dropWhile (fun x ↦ x == 0) (hd :: tl)).head p' = (hd :: tl).head (by simp only [ne_eq,
            not_false_eq_true]) := by
            congr
          rw [this]
          simp only [head_cons, ne_eq]
          exact h
    rw [get_zero_eq_head]
    refine lemma1 l.reverse ?non_empty
    by_contra h
    rw [h] at p
    exact p rfl



def poly_add_non_dropping_zeros  (a b : List R) : List R :=
  match a, b with
    | [], _ => b
    | _, [] => a
    | a::as, b::bs =>
      (a + b) :: (poly_add_non_dropping_zeros as bs)

-- def fmap2 {A B C : Type u} (f: Type u -> Type v) {F: Functor f}:  (A -> B -> C) -> f A -> f B -> f C := by
--   intro g
--   intro a
--   intro b
--   exact Functor.map₂ g a  b8

-- def funtor_succ : (List Nat) -> List Nat := List.map Nat.succ
-- def funtor_add_one : (List Nat) -> List Nat := List.map (fun x => x + 1)
-- def test := Functor.Liftp Nat.add_one [1, 2, 3]

-- def poly_add_non_dropping_zeros'  {R : Type*} [Nontrivial R] [CommRing R] (a b : List R) : List R := (List.map (fun x => a + x))  b
theorem poly_nil_add  (a : List R) : poly_add_non_dropping_zeros [] a = a := by
  unfold poly_add_non_dropping_zeros
  simp only

theorem poly_add_nil  (a : List R) : poly_add_non_dropping_zeros a [] = a := by
  unfold poly_add_non_dropping_zeros
  by_cases h: a = []
  · rw [h]
  · simp only




theorem poly_add_comm  (a b : List R) : poly_add_non_dropping_zeros a b = poly_add_non_dropping_zeros b a := by
  match a, b with
  | [], [] => rfl
  | [], _ =>
    rw [poly_nil_add]
    rw [poly_add_nil]
  | _, [] =>
    rw [poly_nil_add]
    rw [poly_add_nil]
  | a::as, b::bs =>
    apply cons_eq_cons.mpr
    apply And.intro
    · exact add_comm a b
    · exact poly_add_comm as bs

instance temp1 : CommRing (PolynomialList R) where
  add a b := ⟨drop_trailing_zeros  (poly_add_non_dropping_zeros a.coeffs b.coeffs), drop_trailing_zeros_last_non_zero _⟩
  zero := {coeffs := [], non_zero := by simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff]}
  add_zero := by
    intro a
    simp only
    unfold HAdd.hAdd
    unfold instHAdd
    simp only
    congr
  neg := List.map Neg.neg
  add_comm := poly_add_comm
