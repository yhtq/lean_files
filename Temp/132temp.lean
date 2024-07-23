import Mathlib.Algebra.Group.Basic
-- import Mathlib.GroupTheory.Coset
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Setoid.Partition
import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Init.Data.Nat.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Eval
import Mathlib.Data.Set.Card
open Polynomial List Nat Sylow Fintype Setoid Classical
-- 被迫导入 Classical 是因为给出 Sylow 子群的元素个数使用了与 Classical 有关的 instance
variable {G : Type} [Group G] [Fintype G]
theorem only_sylow_subgroup_is_normal  {p: ℕ} [Fact (Nat.Prime p)] : (card (Sylow p G) = 1) -> ∀ (H : Sylow p G), (H: Subgroup G).Normal := by
  intro h
  intro H
  have h2 := card_sylow_eq_card_quotient_normalizer H
  rw [h] at h2
  have : (H: Subgroup G).normalizer = ⊤ := by
    have : Nat.card ((H: Subgroup G).normalizer) = Nat.card G := by
      rw [<-card_eq_fintype_card] at h2
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((H: Subgroup G).normalizer: Subgroup G)]
      rw [<-h2]
      simp
    apply Subgroup.eq_top_of_card_eq _ this
  exact Subgroup.normalizer_eq_top.mp this

theorem have_two_coprime_factor_then_is_not_power (r: ℕ) (n: ℕ) (m: ℕ) (coprime: Coprime m n) (m_ne_one: m ≠ 1) (fac:  n * m ∣ r) : ∀ k: ℕ, r ≠ n^k := by
  intro k
  by_contra h
  rw [h] at fac
  have dvd_1 : m ∣ n * m :=  Nat.dvd_mul_left m n
  have dvd_2 : m ∣ m := Nat.dvd_refl m
  let dvd_3 :=  dvd_trans dvd_1 fac
  have := Nat.Coprime.pow 1 k coprime
  rw [Nat.pow_one] at this
  let r := Nat.eq_one_of_dvd_coprimes this dvd_2 dvd_3
  exact absurd r m_ne_one


theorem has_only_sylow_group_not_simple {p: ℕ} [p_is_p: Fact (Nat.Prime p)]  (single: card (Sylow p G) = 1) (is_prime_factor: p ∣ card G) (non_p_group: ∀n: ℕ, card G ≠ p^n): ¬ IsSimpleGroup G := by
  by_contra cp
  let sylow_group: Sylow p G := default
  let p' := only_sylow_subgroup_is_normal single sylow_group
  -- 利用单群的定义，只需验证唯一的 Sylow 子群非平凡即可
  let p' := IsSimpleGroup.eq_bot_or_eq_top_of_normal  sylow_group p'
  let sylow_group_card := card_eq_multiplicity sylow_group
  rcases p' with (h2 | h2) <;> rw [h2] at sylow_group_card
  ·
    -- 如果 Sylow 子群是整个群，则与 G 不是 p 群矛盾
    have : ¬ (p ∣ card G) := by
      rw [card_eq_nat_card] at sylow_group_card
      rw [Subgroup.card_bot] at sylow_group_card
      let sylow_group_card' := sylow_group_card.symm
      have p_is_prime := p_is_p.out
      have := (cast_pow_eq_one _ _ ?_).mp sylow_group_card'
      · by_contra
        exact absurd this (Nat.Prime.ne_one p_is_prime)
      · have := (
                  Nat.Prime.dvd_iff_one_le_factorization
                  p_is_p.out
                  (Fintype.card_ne_zero : card G ≠ 0)
                  ).mp is_prime_factor
        omega
    exact this is_prime_factor
  ·
    -- 如果 Sylow 子群是 {1}，则由 Sylow 定理与 p 整除 card G 矛盾
    have : card G = p^(card G).factorization p := by
      rw [card_eq_nat_card]
      repeat rw [card_eq_nat_card] at sylow_group_card
      rw [Subgroup.card_top] at sylow_group_card
      exact sylow_group_card
    exact non_p_group ((card G).factorization p) this

theorem finite_subgroups_have_order_and_same_card_is_eq (a b: Subgroup G) (card_eq : card a = card b) (order: a ≤ b) : a = b := by
  apply SetLike.coe_set_eq.mp
  set a':= (a: Set G)
  set b':= (b: Set G)
  apply Set.eq_of_subset_of_card_le order
  have : card a' = card b' := card_eq
  rw [<-this]

structure possible_sylow_groups_card  (p: ℕ)  [Fact (Nat.Prime p)] (q: ℕ) (factor: card G = p * q) (coprime: Coprime p q) where
  possible_set : Finset ℕ
  possible_set_def : possible_set = Finset.filter (λ x => x ≡ 1 [MOD p] ∧  x ∣ q) (Finset.range (q + 1) \ {0})
  p : card (Sylow p G) ∈ possible_set

-- 计算可能的 Sylow p 子群的个数，使用了 Finset.filter，稍后可以直接计算
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
    exact (Subgroup.card_quotient_dvd_card (any_sylow_group).normalizer)
  have lemma_q : card (Sylow p G) ∣ q := by
    rw [factor] at lemma_p
    apply Coprime.dvd_of_dvd_mul_left _ lemma_p
    by_contra h
    let p2 :=  coprime_or_dvd_of_prime is_prime.out $ card (Sylow p G)
    rcases p2 with (h1 | h1)
    · apply Coprime.symm at h1
      exact absurd h1 h
    · exact absurd h1 (not_dvd_card_sylow p G)
  let possible_set := Finset.filter (λ x => x ≡ 1 [MOD p] ∧  x ∣ q) (Finset.range (q + 1) \ {0})
  have lemma_le : card (Sylow p G) ≤  q := Nat.le_of_dvd q_pos lemma_q
  have : card (Sylow p G) ∈ possible_set := by
    unfold_let
    simp
    apply And.intro (lt_succ_of_le lemma_le) (And.intro pn1 lemma_q)
  exact {possible_set := possible_set, possible_set_def := by rfl, p := this}


-- 利用函数值构造类型上的划分
theorem card_eq_card_of_partition_by_func_fin {α β: Type} [Fintype α] [Fintype β] (f: α → β): card α = (∑ i: β, Finset.card ({a: α | f a = i}.toFinset)) := by
  simp only [Set.mem_setOf_eq, Set.toFinset_setOf]
  rw [<-Finset.card_univ]
  let dis_union_partition_fun : β -> Finset α := λ i => {a: α | f a = i}.toFinset
  let card_partition := @Finset.card_biUnion β α _ Finset.univ dis_union_partition_fun ?_
  · unfold_let at card_partition
    simp only [Set.mem_setOf_eq, Set.toFinset_setOf] at card_partition
    rw [<-card_partition]
    apply congr_arg
    apply Finset.ext
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, exists_eq',
      implies_true]
  · intro x _ y _ none_eq
    unfold_let
    simp only [Set.mem_setOf_eq, Set.toFinset_setOf]
    apply Finset.disjoint_filter.mpr
    exact fun x_1 _ h => ne_of_eq_of_ne h none_eq

#check Finset.range

noncomputable def image_f [Fintype α] [DecidableEq β] (f: α -> β)  : Finset β := Finset.image f Finset.univ

-- 上面定义使用集合值域的版本
theorem card_eq_card_of_partition_by_func_image {α β: Type} [Fintype α] [DecidableEq β]  (f: α → β): card α = (∑ i ∈ image_f f, Finset.card ({a: α | f a = i}.toFinset)) := by
  let range_type: Type := image_f f
  let mem_range_type : (x: α) -> f x ∈ image_f f := by
    intro x
    unfold image_f
    simp
  let f' : α -> range_type := λ a => ⟨f a, mem_range_type a⟩
  let partition_result := card_eq_card_of_partition_by_func_fin f'
  unfold_let at partition_result
  simp only [Set.mem_setOf_eq, Set.toFinset_setOf] at partition_result
  simp
  rw [<-(Finset.sum_subtype_of_mem _ (
      (
        fun _ => id
      ) : ∀ x ∈ image_f f, x ∈ image_f f
    ))]
  rw [partition_result]
  apply Finset.sum_congr
  ·
    exact (Eq.symm $ Finset.subtype_eq_univ.mpr (fun _ => id))
  · intro x _
    apply congr_arg
    congr
    ext x1
    rw [<-Subtype.coe_inj]

theorem divide_group_into_elements_by_order (orders: Finset ℕ)  : card G ≥ ∑ i in orders, card {a: G | orderOf a = i} := by
  let full_partition := card_eq_card_of_partition_by_func_image (orderOf: G -> ℕ)
  rw [full_partition]
  apply ge_iff_le.mpr
  have (i: ℕ): {a : G | orderOf a = i}.toFinset.card = card ↑{a : G | orderOf a = i} := Set.toFinset_card {a | orderOf a = i}
  simp_rw [<-this]
  apply le_trans
    (Finset.sum_le_sum_of_ne_zero ?_)
    (Nat.le_of_eq $ Finset.sum_congr rfl (
      by
        intro x _
        -- 理应 rfl 但是不知为何失败了
        simp only [Set.mem_setOf_eq, Set.toFinset_setOf]
    ))
  intro x _ hx
  have := (Finset.card_pos.mp (Nat.zero_lt_of_ne_zero hx)).choose_spec
  unfold image_f
  simp
  simp at this
  exact ⟨_, this⟩

lemma exactly_dvd_fac_eq_one (n: ℕ)(p: ℕ) [is_prime: Fact (Nat.Prime p)] (non_zero: n ≠ 0)(dvd: p ∣ n) (exactly_dvd: ¬ p^2 ∣ n) : n.factorization p = 1 := by
  have fac_more_than_one := (Nat.Prime.dvd_iff_one_le_factorization (is_prime.out) non_zero).mp
  have fac_less_than_one : n.factorization p ≤ 1 := by
    by_contra h
    have : p^2 ∣ n := by
      simp at h
      exact (Nat.Prime.pow_dvd_iff_le_factorization (is_prime.out) non_zero).mpr h
    exact exactly_dvd this
  exact Eq.symm (Nat.le_antisymm (fac_more_than_one dvd) fac_less_than_one)

theorem card_of_sylow_p_group_when_p_exactly_divide_card_of_G (p: ℕ) [is_prime: Fact (Nat.Prime p)] (dvd: p ∣ card G) (exactly_dvd: ¬ p^2 ∣ card G) (G_p : Sylow p G) : card G_p  = p := by
  let sylow_group_card := card_eq_multiplicity G_p
  have card_ne_zero : card G ≠ 0 := Fintype.card_ne_zero
  have : (card G).factorization p = 1 := exactly_dvd_fac_eq_one (card G) p card_ne_zero dvd exactly_dvd
  rw [this] at sylow_group_card
  simp only [pow_one] at sylow_group_card
  exact sylow_group_card

theorem number_of_p_order_ele_in_p_group (p: ℕ) [is_prime: Fact (Nat.Prime p)] (group_ord: card G = p) : card {a: G | orderOf a = p}.toFinset = p - 1 := by
  let t' := card_eq_card_of_partition_by_func_image (λ a: G => orderOf a)
  have : image_f (orderOf : G -> ℕ) = {1, p} := by
    unfold image_f
    apply Finset.ext
    intro x
    rw [Finset.mem_image]
    apply Iff.intro
    · intro h
      let ⟨y, hy⟩ := h
      have : orderOf y ∣ p := group_ord ▸ orderOf_dvd_card
      let t' := (@Nat.dvd_prime p (orderOf y) is_prime.out).mp this
      simp
      rw [<-(hy.2)]
      exact t'
    · intro h
      simp at h
      rcases h with (h | h)
      · use 1
        simp only [orderOf_one]
        exact ⟨Finset.mem_univ 1, h.symm⟩
      ·
        rw [h]
        haveI := isCyclic_of_prime_card group_ord
        let order_p_ele := @IsCyclic.exists_ofOrder_eq_natCard G _ _
        rw [Nat.card_eq_fintype_card] at order_p_ele
        rw [group_ord] at order_p_ele
        let ⟨g, _⟩ := order_p_ele
        use g ,(Finset.mem_univ g)
  simp at t'
  simp at this
  rw [this] at t'
  rw [Finset.sum_insert] at t'
  have order_one : (Finset.filter (fun (x_1: G) ↦ x_1 = 1) Finset.univ).card = 1 := by
    apply Finset.card_eq_one.mpr
    use 1
    apply Finset.ext
    intro a
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, Finset.mem_singleton]
  rw [group_ord] at t'
  simp only [orderOf_eq_one_iff] at t'
  rw [order_one] at t'
  simp at t'
  have :  (Finset.filter (fun (x_1: G) => orderOf x_1 = p) Finset.univ).card = card ({a | orderOf a = p} : Set G) := by
    simp only [Set.coe_setOf, Set.mem_setOf_eq]
    rw [<-Fintype.card_coe]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [this] at t'
  conv =>
    rhs
    rw [t']
  simp
  exact Finset.not_mem_singleton.mpr $ Ne.symm (Nat.Prime.ne_one is_prime.out)

theorem numbers_of_elements_with_order_p_when_exactly_dvd (p: ℕ) [is_prime: Fact (Nat.Prime p)] (dvd: p ∣ card G) (exactly_dvd: ¬ p^2 ∣ card G)
: card {a: G | orderOf a = p} = (p - 1) * (card (Sylow p G)) := by
  let a_subgroup (a: G) := Subgroup.zpowers (a: G)
  let generated_group_has_order_p (a: {a: G | orderOf a = p}) : card (a_subgroup a) = p ^ (card G).factorization p := by
    rw [exactly_dvd_fac_eq_one (card G) p Fintype.card_ne_zero dvd exactly_dvd]
    rw [pow_one]
    let ⟨a', ha⟩ := a
    simp only [Set.mem_setOf_eq]
    rw [Fintype.card_zpowers]
    rw [Set.mem_setOf_eq] at ha
    exact ha
  let generated_sylow_group_of_elements : {a: G | orderOf a = p} -> Sylow p G := fun a => Sylow.ofCard (a_subgroup a) (generated_group_has_order_p a)
  have a_in_generated_group : ∀ a: {a: G | orderOf a = p}, (a: G) ∈ generated_sylow_group_of_elements a := by
    intro a
    have : generated_sylow_group_of_elements a = Sylow.ofCard (a_subgroup a) (generated_group_has_order_p a) := by rfl
    rw [this]
    apply SetLike.mem_coe.mp
    have : ↑(ofCard (a_subgroup a) (generated_group_has_order_p a)) = ((a_subgroup a) : Set G) := by rfl
    rw [this]
    apply SetLike.mem_coe.mpr
    unfold_let
    simp only [Set.mem_setOf_eq, Subgroup.mem_zpowers]
  let partition := card_eq_card_of_partition_by_func_fin generated_sylow_group_of_elements
  let sylow_group_to_order_p_subset (s: Sylow p G) : Finset s := {a: s | orderOf a = p}.toFinset
  have sylow_group_to_order_p_subset_card : ∀ s: Sylow p G, (sylow_group_to_order_p_subset s).card = p - 1 := by
    intro s
    unfold_let
    let r':= number_of_p_order_ele_in_p_group p (card_of_sylow_p_group_when_p_exactly_divide_card_of_G p dvd exactly_dvd s)
    rw [Fintype.card_coe] at r'
    exact r'

  have all_elements_are_generator (h: Sylow p G) (a : {a: G | orderOf a = p}) (in_h : (a: G) ∈ h) : generated_sylow_group_of_elements a = h := by
    have sub : (a_subgroup a) ≤ h := by
      unfold_let
      simp only [Set.mem_setOf_eq]
      rw [Subgroup.zpowers_eq_closure]
      apply (Subgroup.closure_le (h: Subgroup G)).mpr
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact in_h
    have : card (a_subgroup a) = card h := by
      rw [generated_group_has_order_p, card_eq_multiplicity]
    apply Sylow.ext
    apply finite_subgroups_have_order_and_same_card_is_eq
    · exact this
    · exact sub

  have : ∀h: (Sylow p G), {a: {a: G | orderOf a = p} | generated_sylow_group_of_elements a = h}.toFinset.card = p - 1 := by
    intro h
    simp
    have : (Finset.filter (fun x ↦ generated_sylow_group_of_elements x = h) Finset.univ).card = ({x: {a: G | orderOf a = p} | (x: G) ∈ h}.toFinset).card := by
      apply congrArg (Finset.card)
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.toFinset_setOf]
      apply Finset.filter_congr
      intro x _
      apply Iff.intro
      · intro h1
        rw [<-h1]
        exact a_in_generated_group x
      · intro h1
        exact all_elements_are_generator h x h1
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Set.toFinset_setOf] at this
    rw [this]
    unfold_let at sylow_group_to_order_p_subset_card
    let p' := sylow_group_to_order_p_subset_card h
    simp only [Set.mem_setOf_eq, Set.toFinset_setOf] at p'
    rw [<-p']
    apply Finset.card_bij (
      fun (a: { x // orderOf x = p })
        (h1: a ∈ Finset.filter (fun x ↦ ↑x ∈ h) Finset.univ) => ⟨a, by
          simp only [Finset.mem_filter,
            Finset.mem_univ, true_and] at h1
          exact h1⟩
    )
    · intro a h1
      simp
      exact a.2
    · intro a h1
      -- simp only [Finset.mem_filter, Finset.mem_univ, Subgroup.orderOf_mk, true_and]
      -- intro a' h2 h'
      -- simp only [Subtype.mk.injEq] at h'
      -- apply Subtype.coe_inj.mp
      -- exact h'
      aesop
    · intro b hb
      aesop
      -- simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      -- use ⟨b, by simp; exact hb⟩
      -- simp only [Subtype.coe_eta, Finset.mem_filter, Finset.mem_univ, SetLike.coe_mem, and_self,
      --   exists_const]
  have : (fun (s :Sylow p G) => {a: {a: G | orderOf a = p} | generated_sylow_group_of_elements a = s}.toFinset.card) = p - 1 := by
    funext h
    simp
    simp at this
    apply this h
  rw [this] at partition
  simp at partition
  simp
  rw [mul_comm]
  exact partition

lemma order_of_ele_in_p_group_is_pow_of_p {p: ℕ} [is_prime: Fact (Nat.Prime p)] (is_p_group: card G = p^n) : ∀x : G, ∃k < n + 1, orderOf x = p ^ k := by
  intro x
  have : orderOf x ∣ p^n := by
    rw [<-is_p_group]
    exact orderOf_dvd_card
  let ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow (is_prime.out)).mp this
  use k
  apply And.intro
  ·
    exact lt_succ_of_le hk
  ·
    exact hk'

theorem numbers_of_p_group_divide_into_orders {n: ℕ} {p: ℕ} [is_prime: Fact (Nat.Prime p)] (is_p_group: card G = p^n): p^n = ∑ i ∈ Finset.range (n+1), card {a: G | orderOf a = p^i} := by
  set func: G -> ℕ := orderOf with h_func
  set p_power: ℕ -> ℕ := λ i => p^i with h_p_power
  rw [<-is_p_group]
  rw [card_eq_card_of_partition_by_func_image func]
  have : ∑ i ∈ Finset.range (n + 1), card {a: G | orderOf a = p^i} = ∑ i ∈ Finset.image p_power (Finset.range (n+1)), {a | func a = i}.toFinset.card := by
    rw [Finset.sum_image (
      by
        intro x _ y _ h
        unfold_let at h
        let t := @Nat.pow_right_injective p (Prime.two_le is_prime.out)
        exact t h
      )]
    apply Finset.sum_congr rfl
    intro x _
    unfold_let
    simp
    exact card_subtype fun x_1 ↦ orderOf x_1 = p ^ x
  rw [this]
  apply Finset.sum_subset_zero_on_sdiff
  · unfold_let
    unfold image_f
    rw [<-h_p_power, <-h_func]
    apply Finset.image_subset_iff.mpr
    intro x _
    apply Finset.mem_image.mpr
    unfold_let
    simp only [Finset.mem_range]
    rcases order_of_ele_in_p_group_is_pow_of_p is_p_group x with ⟨k, hk, hk'⟩
    use k
    exact And.intro hk hk'.symm

  · intro x hx
    simp  at hx
    let ⟨_, hx_2⟩ := hx
    unfold image_f at hx_2
    unfold_let
    aesop
  · intro _ _
    -- simp
    rfl
theorem have_exactly_numbers_of_elements_with_order_p_n_then_unique (p : ℕ) [is_prime: Fact (Nat.Prime p)]  :∑ i ∈ Finset.range (Nat.factorization (card G) p+1), card {a: G | orderOf a = p^i} ≤ p ^ (Nat.factorization (card G) p) -> card (Sylow p G) = 1 := by
  intro h_c
  by_contra h'
  have non_trivial : Nontrivial (Sylow p G) := by
    apply Fintype.one_lt_card_iff_nontrivial.mp
    let non_zero := @Fintype.card_ne_zero (Sylow p G) _ _
    omega
  let exists_pair := @Nontrivial.exists_pair_ne (Sylow p G) non_trivial
  let ⟨x, y, hxy⟩ := exists_pair
  set sylow_card := p ^ (Nat.factorization (card G) p) with h_sylow_card
  have p_sylow_card : ∀ s: (Sylow p G), card s = sylow_card := by
    intro s
    rw [Sylow.card_eq_multiplicity]
  have sylow_is_p_group : ∀ s: (Sylow p G), card s = p ^ (Nat.factorization (card G) p) := h_sylow_card ▸ p_sylow_card
  wlog h: ∃ a: G, a ∈ x ∧ a ∉ y
  · have sym : ∃ a: G,  a ∈  y ∧  a ∉  x := by
      by_contra h'
      simp only [not_exists, not_and] at h'
      simp only [not_exists, not_and, Decidable.not_not] at h
      let p := SetLike.ext_iff.mpr.mt hxy
      simp only [not_forall] at p
      rcases p with ⟨a, p⟩
      let ha := h a
      let p' := Classical.not_iff.mp p
      let hap := p'.mpr ∘ ha
      simp only [imp_not_self] at hap
      have := p'.mp hap
      have := h' a this
      exact absurd hap this
    exact (@this G _ _ p _  h' non_trivial y x (hxy.symm) h_c rfl p_sylow_card sylow_is_p_group sym )
  · rcases h with ⟨a, hax, hay⟩
    rw [h_sylow_card, numbers_of_p_group_divide_into_orders (sylow_is_p_group y)] at h_c
    set sum_set := Finset.range ((card G).factorization p + 1)
    let f_inj_i (i: ℕ) : {a: y | orderOf a = p ^ i} -> {a: G | orderOf a = p ^ i} := fun a => ⟨a, by
        simp only [Set.mem_setOf_eq,
        orderOf_submonoid]
        exact a.2⟩
    have f_inj_is_inj (i: ℕ) : Function.Injective (f_inj_i i) := by
      intro x y hx
      unfold_let at hx
      simp at hx
      exact Subtype.coe_inj.mp hx
    have card_on_x_lt_card_on_G : ∀i ∈ sum_set, card {a: y | orderOf a = p ^ i} ≤ card {a: G | orderOf a = p ^ i} := fun i _ => Fintype.card_le_of_injective (f_inj_i i) (f_inj_is_inj i)
    have : ∑ i ∈ sum_set, card {a: y | orderOf a = p ^ i} ≤ ∑ i ∈ sum_set, card {a: G | orderOf a = p ^ i} := GCongr.sum_le_sum card_on_x_lt_card_on_G
    have := _root_.le_antisymm this h_c
    let card_on_x_eq_card_on_G := (Finset.sum_eq_sum_iff_of_le card_on_x_lt_card_on_G).mp this
    set order_of_a := orderOf a
    rcases order_of_ele_in_p_group_is_pow_of_p (sylow_is_p_group x) ⟨a, hax⟩ with ⟨k, hk, hk'⟩
    simp only [Subgroup.orderOf_mk] at hk'
    have k_in_sum_set : k ∈ sum_set := by
      unfold_let
      simp only [Finset.mem_range]
      exact hk
    have : card {a: y | orderOf a = p ^ k} < card {a: G | orderOf a = p ^ k} := by
      apply @Fintype.card_lt_of_injective_of_not_mem _ _ _ _ (f_inj_i k) (f_inj_is_inj k) ⟨a, by simp; exact hk'⟩
      by_contra h_r
      simp at h_r
      rcases h_r with ⟨a1, h_r'⟩
      rcases h_r' with ⟨h_a_1, h_a_1', h_a_1''⟩
      unfold_let at h_a_1''
      simp at h_a_1''
      rw [h_a_1''] at h_a_1
      exact absurd h_a_1 hay
    rw [card_on_x_eq_card_on_G k k_in_sum_set] at this
    exact Nat.lt_irrefl (card {a: G | orderOf a = p ^ k}) this


theorem not_simple_132 {G : Type} [Group G] [Fintype G] (h : card G = 132) : ¬ IsSimpleGroup G := by
  by_contra cp
  set n11 := card (Sylow 11 G) with hn11
  have : Fact (Nat.Prime 11) := by norm_num; apply fact_iff.mpr; simp only
  have : n11 ∈ ({1, 12}: Finset ℕ) := by
    have is_prime_11 : Fact (Nat.Prime 11) := by norm_num; apply fact_iff.mpr; simp only
    let _res  := get_possible_sylow_groups_card 11 12 (by rw [h]) (by norm_num)
    let res_def := _res.possible_set_def
    let p := _res.p
    -- #eval Finset.filter (fun x ↦ x ≡ 1 [MOD 11] ∧ x ∣ 12) (Finset.range (12 + 1) \ {0})
    have : _res.possible_set = {1, 12} := by
      rw [res_def]
      decide
    exact this ▸ p
  simp at this
  rcases this with (h1 | h1)
  have : ∀n: ℕ , 132 ≠ 11 ^n := by
    apply have_two_coprime_factor_then_is_not_power 132 11 12 <;> norm_num

  · let r := has_only_sylow_group_not_simple h1 (by rw [h];norm_num) (by rw [h]; exact this )
    exact r cp
  ·
    let order_11 := @numbers_of_elements_with_order_p_when_exactly_dvd G _ _ 11 _ (by rw [h]; norm_num) (by rw [h]; norm_num)
    rw [<-hn11] at order_11
    rw [h1] at order_11
    simp only [Set.coe_setOf, Set.mem_setOf_eq, reduceSub, reduceMul] at order_11
    let order_3 := @numbers_of_elements_with_order_p_when_exactly_dvd G _ _ 3 _ (by rw [h]; norm_num) (by rw [h]; norm_num)
    set n3 := card (Sylow 3 G) with hn3
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
        apply have_two_coprime_factor_then_is_not_power 132 3 44 <;> norm_num
      let r := has_only_sylow_group_not_simple h2 (by rw [h];norm_num) (by rw [h]; exact this)
      exact r cp
    ·
      rw [h2] at order_3
      simp at order_3
      let all_elements_counts := @divide_group_into_elements_by_order G _ _ (({1, 3, 11, 2, 4}: Set ℕ).toFinset)
      simp at all_elements_counts
      rw [h, order_3, order_11] at all_elements_counts
      -- 手动做加法的约化
      have : 132 = 1 + (8 +(120 + 3)) := by
        norm_num
      rw [this] at all_elements_counts
      repeat apply (add_le_add_iff_left _).mp at all_elements_counts
      apply (add_le_add_iff_left 1).mpr at all_elements_counts
      let r := @have_exactly_numbers_of_elements_with_order_p_n_then_unique G _ _ 2
      have : (card G).factorization 2 = 2 := by
        rw [h]
        native_decide
      rw [this] at r
      simp at r
      have : card (Sylow 2 G) = 1 := by
        apply r
        have : Finset.range 3 = {0, 1, 2} := by
          rfl
        rw [this]
        simpa
      have non_power : ∀n: ℕ , 132 ≠ 2 ^n := by
        apply have_two_coprime_factor_then_is_not_power 132 2 33 <;> norm_num
      let r := has_only_sylow_group_not_simple this (by rw [h]; norm_num) (h ▸ non_power)
      exact absurd cp r
    ·
      rw [h2] at order_3
      simp at order_3
      let all_elements_counts := @divide_group_into_elements_by_order G _ _ (({3, 11}: Set ℕ).toFinset)
      simp at all_elements_counts
      rw [order_3, order_11, h] at all_elements_counts
      simp at all_elements_counts
#print axioms not_simple_132

-- example {F : Type*} [Field F] [Fintype F] [IsAlgClosed F] : False := by
--   let f: F[X] := ∏ i : F, (X - C i)
