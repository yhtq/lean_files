import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Group.Basic
import Mathlib.GroupTheory.Coset
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.FieldTheory.Finite.GaloisField
import Init.Data.Nat.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Eval
import Mathlib.Data.Set.Card
open Polynomial List Nat Sylow Fintype Setoid

variable {G : Type} [Group G] [Fintype G] {p: ℕ}

theorem only_sylow_subgroup_is_normal  [Fact (Nat.Prime p)] : (card (Sylow p G) = 1) -> ∀ (H : Sylow p G), (↑H: Subgroup G).Normal := by
  intro h
  intro H
  have h2 := card_sylow_eq_card_quotient_normalizer H
  rw [h] at h2
  have : (↑H: Subgroup G).normalizer = ⊤ := by
    have : Nat.card ((↑H: Subgroup G).normalizer) = Nat.card G := by
      rw [<-card_eq_fintype_card] at h2
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((↑H: Subgroup G).normalizer: Subgroup G)]
      rw [<-h2]
      simp
    apply Subgroup.eq_top_of_card_eq
    exact this
  apply Subgroup.normalizer_eq_top.mp
  exact this

theorem has_only_sylow_group_not_simple [p_is_p: Fact (Nat.Prime p)]  (single: card (Sylow p G) = 1) (is_prime_factor: p ∣ card G) (non_p_group: ∀n: ℕ, card G ≠ p^n): ¬ IsSimpleGroup G := by
  by_contra cp
  let sylow_group: Sylow p G := default
  let p' := only_sylow_subgroup_is_normal single sylow_group
  let p' := @IsSimpleGroup.eq_bot_or_eq_top_of_normal G _ cp sylow_group p'
  let sylow_group_card := card_eq_multiplicity sylow_group
  rcases p' with (h2 | h2) <;> rw [h2] at sylow_group_card
  · have : ¬ (p ∣ card G) := by
      -- rw [card_eq_nat_card]
      rw [card_eq_nat_card] at sylow_group_card
      rw [Subgroup.card_bot] at sylow_group_card
      have p_is_prime : Nat.Prime p := p_is_p.out
      have : (card G).factorization p = 0 := by
        by_contra h
        have : (card G).factorization p ≠ 0 := by
          apply h
        let p' := (@Nat.cast_pow_eq_one ℕ _ _ p ((card G).factorization p) this).mp sylow_group_card.symm
        apply Nat.Prime.ne_one p_is_prime p'
      let ca := (factorization_eq_zero_iff (card G) p).mp this
      rcases ca with (h1 | h1 | h1)
      · contradiction
      · exact h1
      · exact absurd h1 card_ne_zero
    exact this is_prime_factor
  · have : card G = p^(card G).factorization p := by
      rw [card_eq_nat_card]
      repeat rw [card_eq_nat_card] at sylow_group_card
      rw [Subgroup.card_top] at sylow_group_card
      exact sylow_group_card
    let non_p_group' := non_p_group ((Nat.card G).factorization p)
    simp at non_p_group'
    contradiction



structure possible_sylow_groups_card  (p: ℕ)  [Fact (Nat.Prime p)] (q: ℕ) (factor: card G = p * q) (coprime: Coprime p q) where
  possible_set : Finset ℕ
  possible_set_def : possible_set = Finset.filter (λ x => x ≡ 1 [MOD p] ∧  x ∣ q) (Finset.range (q + 1) \ {0})
  p : card (Sylow p G) ∈ possible_set

-- 计算可能的Sylow p子群的个数
def get_possible_sylow_groups_card (p: ℕ)  [is_prime: Fact (Nat.Prime p)] (q: ℕ) (factor: card G = p * q) (coprime: Coprime p q): possible_sylow_groups_card p q factor coprime:= by
  let pn1 := card_sylow_modEq_one p G
  let any_sylow_group : Sylow p G := default
  have q_pos : q > 0 := by
    by_contra h
    simp at h
    rw [h] at factor
    norm_num at factor
  have lemma_p : card (Sylow p G) ∣ card G := by
    rw [card_sylow_eq_card_quotient_normalizer any_sylow_group]
    repeat rw [<-card_eq_fintype_card]
    apply (Subgroup.card_quotient_dvd_card (any_sylow_group).normalizer)
  have lemma_q : card (Sylow p G) ∣ q := by
    rw [factor] at lemma_p
    apply @Coprime.dvd_of_dvd_mul_left (card (Sylow p G)) p q
    · by_contra h
      let p2 :=  @coprime_or_dvd_of_prime p (is_prime.out) (card (Sylow p G))
      rcases p2 with (h1 | h1)
      · apply Coprime.symm at h1
        exact absurd h1 h
      · exact absurd h1 (not_dvd_card_sylow p G)
    · exact lemma_p
  let possible_set := Finset.filter (λ x => x ≡ 1 [MOD p] ∧  x ∣ q) (Finset.range (q + 1) \ {0})
  have lemma_le : card (Sylow p G) ≤  q := by
      apply Nat.le_of_dvd q_pos lemma_q
  have : card (Sylow p G) ∈ possible_set := by
    have : card (Sylow p G) ∈ Finset.filter (λ x => x ≡ 1 [MOD p] ∧  x ∣ q) (Finset.range (q + 1) \ {0}) := by
      simp
      apply And.intro
      · exact lt_succ_of_le lemma_le
      · apply And.intro
        · exact pn1
        · exact lemma_q
    exact this
  exact {possible_set := possible_set, possible_set_def := by rfl, p := this}

structure partition_by_func {α β: Type} (f: α → β)  where
  classes: Set (Set α) := {s | ∃i: β ,  s = {a: α | f a = i} ∧  s ≠ ∅}
  equivalance_relation : Setoid α := {
    r := λ a b => f a = f b
    iseqv := {
      refl := by intro x; rfl
      symm := by intros x y h; exact Eq.symm h
      trans := by intros x y z; exact Eq.trans
    }
  }
  is_classes : equivalance_relation.classes = classes
  partition_def : classes = {s | ∃i: β ,  s = {a: α | f a = i} ∧  s ≠ ∅} := by rfl

def get_partition_by_func  (f: α → β) : partition_by_func f :=
{
  is_classes := by
    unfold Setoid.classes
    apply Set.ext
    intro x
    unfold Setoid.Rel
    unfold r
    simp
    apply Iff.intro
    · simp
      intro a h
      apply And.intro
      · use f a
      · rw [h]
        exact ne_of_mem_of_not_mem' rfl fun a ↦ a
    · simp
      intro b h ne
      rw [h]
      have : ∃ a: α, f a = b := by
        by_contra h'
        simp at h'
        have : x = ∅ := by
          rw [h]
          apply Set.ext
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          exact h'
        exact absurd this ne
      rcases this with ⟨a, h1⟩
      use a
      rw [h1]
}

def partition_by_func_is_partion  (f: α → β) : IsPartition ((get_partition_by_func f).classes)  := (get_partition_by_func f).is_classes ▸ Setoid.isPartition_classes (get_partition_by_func f).equivalance_relation

noncomputable instance [Fintype α] (s: Set α) : Fintype s := by
  have : Set.Finite s := by
    toFinite_tac
  have : Finite s := Set.Finite.to_subtype this
  exact @Fintype.ofFinite s this


theorem card_eq_sum_card_of_partition [Fintype α] (classes: Set (Set α)) (is_p : IsPartition classes) : card α = (∑ i ∈  classes, Finset.card (i.toFinset)) := by
  sorry

theorem card_eq_card_of_partition_by_func [Fintype α] {α β: Type} (f: α → β) : card α = (∑ i ∈  (get_partition_by_func f).classes, Finset.card (i.toFinset)) := by

theorem divide_group_into_elements_by_order (orders: Finset ℕ) (factor: ∀i ∈ orders, i ∣ card G) : card G ≤ ∑ i in orders, card {a: G | orderOf a = i} := by
  -- have : (@Finset.univ G) =  (⋃ i: ℕ,  {a: G | orderOf a = i})  := by
  --   sorry
  let partition_by_order := get_partition_by_func (λ a: G => orderOf a)
  let is_partition := partition_by_order.is_partition

theorem not_simple_132 {G : Type} [Group G] [Fintype G] (h : card G = 132) : ¬ IsSimpleGroup G := by
  by_contra cp
  let n11 := card (Sylow 11 G)
  have : Fact (Nat.Prime 11) := by norm_num; apply fact_iff.mpr; simp only
  let pn11 := card_sylow_modEq_one 11 G
  let any_11_sylow_group : Sylow 11 G := default
  let sylow_group_card := card_eq_multiplicity any_11_sylow_group
  rw [h] at sylow_group_card
  simp at sylow_group_card
  have cal : 11 ^ ((Nat.factorization 132) 11) = 11 := by
    have : Nat.factorization 132 11 = 1 := by
      have : 132 = 11 * 12 := by norm_num
      rw [this]
      rw [@factorization_eq_of_coprime_left 11 11 12 (by norm_num)]
      rw [@Prime.factorization_self 11 (by norm_num)]
      norm_num
    rw [this]
    rw [pow_one]
  rw [cal] at sylow_group_card
  have : n11 ∈ ({1, 12}: Finset ℕ) := by
    have is_prime_11 : Fact (Nat.Prime 11) := by norm_num; apply fact_iff.mpr; simp only
    let _res  := get_possible_sylow_groups_card 11 12 (by rw [h]) (by norm_num)
    let res := _res.possible_set
    let res_def := _res.possible_set_def
    let p := _res.p
    have : _res.possible_set = {1, 12} := by
      rw [res_def]
      decide
    exact this ▸ p

  simp at this
  rcases this with (h1 | h1)
  have : ∀n: ℕ , 132 ≠ 11 ^n := by
    intro n
    by_contra h
    have : 12 ∣ 11^n := by
      rw [<-h]
      norm_num
    sorry
  · let r := has_only_sylow_group_not_simple h1 (by rw [h];norm_num) (by rw [h]; exact this )
    exact r cp
  · let n3 := card (Sylow 3 G)
    have : n3 ∈ ({1, 4, 22}: Finset ℕ) := by
      let res := get_possible_sylow_groups_card 3 44 (by rw [h]) (by norm_num)
      let p := res.p
      let res_def := res.possible_set_def
      have : res.possible_set = {1, 4, 22} := by
        rw [res_def]
        decide
      exact this ▸ p
    simp at this
    rcases this with (h2 | h2 | h2)
    ·
      have : ∀n: ℕ , 132 ≠ 3 ^n := by
        intro n
        by_contra h
        have : 44 ∣ 3^n := by
          rw [<-h]
          norm_num
        sorry
      let r := has_only_sylow_group_not_simple h2 (by rw [h];norm_num) (by rw [h]; exact this )
      exact r cp
    · let sylow_groud_card3 (g: Sylow 3 G) := card_eq_multiplicity g
      rw [h] at sylow_groud_card3
      simp at sylow_groud_card3
      have : 3 ^ (Nat.factorization 132) 3 = 3 := by
        sorry
      rw [this] at sylow_groud_card3
      sorry
    sorry
