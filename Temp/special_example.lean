-- 著者：秦宇轩

import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic

-- Let `A` and `B` be two subgroups of group `G`.
-- Prove that `A ⊔ B ` is a subgroup of `G` if and only if
-- `A <= B` or `B <= A`.
--
-- Furthermore,
-- prove that group `G` cannot be expressed as the union of two proper subgroups.

lemma noob {S : Type*} {A B : Set S} (h : (¬ A ⊆ B)) :
  (∃ a : S, a ∈ A \ B) := by exact Set.not_subset.mp h

lemma Subgroup.union_subgroup_iff {G : Type*} [Group G] {A B : Subgroup G} :
  (∃ C : Subgroup G , C.carrier = (A.carrier ∪ B.carrier) )
  ↔
  (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := by
    constructor
    · intro foo
      obtain ⟨C, cab⟩ := foo
      -- By contradiction, there exists `a ∈ A \ B` and `b ∈ B \ A`.
      -- Since `C` is a group, `a * b ∈ C = A ∪ B`,
      -- so either `a * b ∈ A` or `a * b ∈ B`,
      -- but both lead to contradiction.
      by_contra no
      push_neg at no
      obtain ⟨ab, ba⟩ := no
      obtain ⟨a, aNotInB⟩ := noob ab
      obtain ⟨b, bNotInA⟩ := noob ba
      have ac : A.carrier ⊆ C.carrier := by
        rw [cab]
        exact Set.subset_union_left
      have abInC : a * b ∈ C.carrier := by
        apply C.mul_mem' <;> rw [cab]; simp only [Set.mem_union]
        · exact Or.inl $ Set.mem_of_mem_diff aNotInB
        · exact Or.inr $ Set.mem_of_mem_diff bNotInA

      have : a * b ∈ A.carrier ∨ a * b ∈ B.carrier :=  (Set.mem_union (a * b) A.carrier B.carrier).mp (cab ▸ abInC)
      wlog abInA : a * b ∈ A.carrier
      · sorry
      · sorry
    · intro foo
      rcases foo with ab | ba
      · use B
        exact Eq.symm (Set.union_eq_self_of_subset_left ab)
      · use A
        exact Eq.symm (Set.union_eq_self_of_subset_right ba)

example (G : Type*) [Group G] : ¬ ∃ A B : Subgroup G,
  (A < ⊤ ∧ B < ⊤)
  ∧
  A.carrier ∪ B.carrier = Set.univ := by
    intro foo
    rcases foo with ⟨A, B, ⟨⟨aProper, bProper⟩, abUniv⟩⟩
    have aNotTop : A.carrier ≠ ⊤ := by exact LT.lt.ne_top aProper
    have bNotTop : B.carrier ≠ ⊤ := by exact LT.lt.ne_top bProper
    have : (A.carrier ⊆ B.carrier) ∨ (B.carrier ⊆ A.carrier) := by
      apply Subgroup.union_subgroup_iff.mp
      use ⊤
      rw [eq_comm]
      exact abUniv
    rcases this with bBig | aBig
    · apply bNotTop
      have : A.carrier ∪ B.carrier = B.carrier := by
        exact Set.union_eq_self_of_subset_left bBig
      rw [this] at abUniv
      exact abUniv
    · apply aNotTop
      have : A.carrier ∪ B.carrier = A.carrier := by
        exact Set.union_eq_self_of_subset_right aBig
      rw [this] at abUniv
      exact abUniv
class Fun where
  a: ℕ
instance  : (Module ℤ ℚ) := by
  constructor
#check Exists.
#check (Module)
