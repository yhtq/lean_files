import Mathlib

-- used for termination
@[local instance]
instance {A : Type u} [DecidableEq A] [Fintype A] : WellFoundedRelation (Finset A) where
  rel a b := a > b
  wf := wellFounded_gt

def Finset.trunc_choose {A : Type u} [DecidableEq A] (s : Finset A) (h : s.Nonempty) : Trunc {a: A // a ∈ s} := by
  apply truncOfCardPos
  simp [h]

-- use Trunc monad as a wrapper for computable results
def permutation_is_product_of_transpositions
    {A : Type u} [DecidableEq A] [Fintype A]
    (sigma : Equiv.Perm A)
    -- use a subtype as goal to make the proof is also computable
    : Trunc {l : List (Equiv.Perm A) // (∀ e ∈ l, ∃ x y, e = Equiv.swap x y) ∧ l.prod = sigma} := by
  let fixed_points (f: Equiv.Perm A) := (Function.fixedPoints f).toFinset
  have mem_fixed_points_iff (f: Equiv.Perm A) (x: A) : x ∈ fixed_points f ↔ f x = x := by
    unfold fixed_points
    simp [Function.IsFixedPt]
  by_cases h: fixed_points sigma = Finset.univ
  · -- if all points are fixed, the result is trivial
    specialize mem_fixed_points_iff sigma
    simp [h] at mem_fixed_points_iff
    have : sigma = 1 := Equiv.ext mem_fixed_points_iff
    apply pure
    use []
    simp [this]
  · -- otherwise, take a non fixed element
    -- for computability, we use a trunc choose, which is a wrapper for non-deterministic choice
    -- make proof in a do-notation
    exact do
      let a <- ((Finset.univ: Finset A) \ fixed_points sigma).trunc_choose (
        by simp [Finset.sdiff_nonempty, h]
      )
      let b := sigma a
      let sigma' := Equiv.swap a.1 b * sigma
      have not_eq_a : sigma a ≠ a := by
        specialize mem_fixed_points_iff sigma a
        simp [mem_fixed_points_iff.not.symm]
        have := a.2
        exact Finset.mem_compl.mp this
      have not_fixed : b ∉ fixed_points sigma := by
        have := a.property
        unfold b
        simp [mem_fixed_points_iff, not_eq_a]
      -- decrease a non fixed point by append swap a b
      let sigma' := Equiv.swap a.1 b * sigma
      -- this lemma is only used for termination
      have fixed_points_increasing : (fixed_points sigma) < (fixed_points sigma') := by
        simp
        apply (Finset.ssubset_iff_of_subset ?_).mpr
        · use a -- a is a fixed point of sigma'
          unfold sigma'
          simp [mem_fixed_points_iff]
          exact not_eq_a
        · intro x hx
          unfold sigma'
          simp [mem_fixed_points_iff] at hx ⊢
          simp [hx, Equiv.swap_apply_def]
          -- here x is a fixed point, so it can't be a or b
          split <;> aesop
      let ⟨l', hl'⟩ <- permutation_is_product_of_transpositions sigma'
      pure ⟨Equiv.swap a b :: l', by constructor <;> aesop⟩
termination_by ((Function.fixedPoints sigma).toFinset)
decreasing_by exact fixed_points_increasing

#eval (Functor.map Subtype.val $ permutation_is_product_of_transpositions (A := Fin 3) (c[0, 1, 2])).unquot
