import Mathlib
-- 1. On the one hand, if S is a complete lattice, the following properties are trivial.
-- 2. On the other hand, the inf of A is given by the greatest lower bound of $A$, and the sup is given by the greatest lower bound of:
--     $$
--     \{a: S | a \space \text{is a upper bound of } A\}
--     $$

-- CompleteLattice is a complete structure rather than props on PartialOrder, so we must declare that they have compatible PartialOrder
example (S: Type*) [p: PartialOrder S]:
  (∃ cl: CompleteLattice S, cl.toPartialOrder = p)
    <-> (
      (∃ x: S, IsGreatest (Set.univ: Set S) x)
      ∧ ∀ A: Set S, A ≠ ∅ -> ∃ infA: S, IsGLB A infA
      ) := by
  constructor
  · intro h
    -- these properties are trivial. just a little instance conversion
    let ⟨cl, clp⟩ := h
    constructor
    · use ⊤
      simp only [isGreatest_univ_iff]
      unfold IsTop
      intro b
      -- convert is a useful tactic when two equal instance are used
      convert CompleteLattice.le_top b
      exact clp.symm
    · intro A hA
      use sInf A
      convert isGLB_sInf A
      exact clp.symm
  · intro h
    have every_set_has_a_glb: ∀ A: Set S, ∃ infA: S, IsGLB A infA := by
      intro A
      by_cases h1: (A = ∅)
      ·
        -- actually, GLB of ∅ is the top element
        rw [h1]
        simp
        let ⟨x, hx⟩ := h.1
        use x
        exact isGreatest_univ_iff.mp hx
      ·
        exact h.2 A h1
    -- for convenience, we firstly define InfSet S
    letI : InfSet S := {
      sInf := fun A => Classical.choose (every_set_has_a_glb A),
    }
    use {
      -- some important fields, actually they are the easy
      sInf_le := fun A => by
        intro a ha
        show Classical.choose (every_set_has_a_glb A) ≤ a
        have := Classical.choose_spec (every_set_has_a_glb A)
        -- obvoisuly, GLB is a lower bound
        have := isGLB_iff_le_iff.mp this (Classical.choose (every_set_has_a_glb A))
        simp at this
        exact this ha
      le_sInf := fun A => by
        intro a ha
        show a ≤ Classical.choose (every_set_has_a_glb A)
        have := Classical.choose_spec (every_set_has_a_glb A)
        have a_is_lb: a ∈ lowerBounds A := ha
        -- if a is a lower bound, then a is less than GLB
        have := isGLB_iff_le_iff.mp this a
        simp [a_is_lb] at this
        exact this
      sSup := fun A => Classical.choose (every_set_has_a_glb $ upperBounds A),
      le_sSup := fun A => by
        intro a ha
        show a ≤ Classical.choose (every_set_has_a_glb $ upperBounds A)
        have := Classical.choose_spec (every_set_has_a_glb $ upperBounds A)
        -- IsGLB of upperBounds A is equal IsLUB of A, the others are same as above
        simp at this
        have := isLUB_iff_le_iff.mp this $ Classical.choose (every_set_has_a_glb $ upperBounds A)
        simp at this
        exact this ha
      sSup_le := fun A => by
        intro a ha
        show Classical.choose (every_set_has_a_glb $ upperBounds A) ≤ a
        have := Classical.choose_spec (every_set_has_a_glb $ upperBounds A)
        -- IsGLB of upperBounds A is equal IsLUB of A, the others are same as above
        simp at this
        have a_is_ub: a ∈ upperBounds A := ha
        have := isLUB_iff_le_iff.mp this a
        simp [a_is_ub] at this
        exact this
      -- other fields are boring, docs says we can use below tricks to def them
      __ := completeLatticeOfInf S (by
          intro A
          exact Classical.choose_spec _
        )
    }
    -- the instance conversion property is rfl
    rfl
