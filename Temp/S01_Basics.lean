import Mathlib
section Exercise_234

/-
1、首先要得到K < H < G的表述。（这里复制了老师的代码）
  （1）也就是说，H是G的子群，K是G的子群，那么K是G的子群
  （2）并且K作为H的子群与作为G的子群的外延是一致的
2、然后证明K是G的正规子群时，也是H的正规子群
  这是由于K中元素经过G中元素取共轭后仍在K中，那么对于H中元素取共轭后，仍然在K中
3、最后找到反例：K是H的正规子群，H是G的正规子群，但是K不是G的正规子群
  我们选择G=S4 H=K4=Z2×Z2（S4中唯二非平凡正规子群为K4和A4） K=Z2
  （1）证明H是G的子群，简单验证即可
  （2）证明H是交换群，对每对元素验证交换律
  （3）证明K是H的子群，如乘法封闭性可以对其中唯二元素分别验证
  （4）证明H是G的正规子群，这只需要对每个H中元素和S4中每个对换（因为S4由对换生成）验证即可
  （5）证明K是H的正规子群，直接使用交换群的子群皆正规的结论
  （6）证明K不是G的正规子群，用反证法，这里取K中元素(0,1)(2,3)，G中元素(0,2)
      验证(0,2)(0,1)(2,3)(0,2)=(0,3)(1,2)不在K中，即得证
-/


--（1）也就是说，H是G的子群，K是G的子群，那么K是G的子群
def Subgroup.to_subgroup (G : Type*) [Group G] {H : Subgroup G} (K : Subgroup H) : Subgroup G where
  --巧妙转换了类型
  carrier := { g : G | ∃ x : H, x ∈ K ∧ x.val = g}
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨x, ⟨hx, ha⟩⟩
    rcases hb with ⟨y, ⟨hy, hb⟩⟩
    --如这里的x和a，x在K中，用来证明乘法封闭性，而a在G中，其值与x相同，即得到了关于a的封闭性
    use x * y
    constructor
    · exact (Subgroup.mul_mem_cancel_right K hy).mpr hx
    · rw [← ha, ← hb]
      rfl
  one_mem' := by
    use 1
    constructor
    · exact Subgroup.one_mem K
    · rfl
  inv_mem' := by
    intro a ha
    rcases ha with ⟨x, ⟨hx, ha⟩⟩
    use x⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff K).mpr hx
    · rw [← ha]
      rfl
--为避免重名
variable (G1 : Type*) [Group G1] {H1 : Subgroup G1} (K1 : Subgroup H1)
--证明我们上述定义的（K作为G的子群）是H的子群
theorem Subgroup.to_subgroup_le : to_subgroup G1 K1 ≤ H1 := by
  intro a ha
  rcases ha with ⟨x, ⟨_, ha⟩⟩
  rw [← ha]
  exact x.property

#check Subtype.val_inj
#check Subgroup.Normal.conj_mem
--（2）并且K作为H的子群与作为G的子群的外延是一致的
theorem Subgroup.to_subgroup_mem (g : H1) : g.val ∈ to_subgroup G1 K1 ↔ g ∈ K1 := by
  constructor
  --(→)通过等词与↑的关系得到
  · intro hg
    rcases hg with ⟨x, ⟨hx, hg⟩⟩
    apply Subtype.val_inj.mp at hg
    rw [← hg]
    exact hx
  --(←)则较简单
  · intro hg
    use g
--2、然后证明K是G的正规子群时，也是H的正规子群
theorem Subgroup.Normal_to_small_Normal : (to_subgroup G1 K1).Normal → K1.Normal :=by
  intro NnG
  refine { conj_mem := ?conj_mem }
  intro k hk h
  simp only [← to_subgroup_mem] at hk
  --由于K中元素经过G中元素取共轭后仍在K中
  have NnG':∀ g:G1,g*k*g⁻¹ ∈ (to_subgroup G1 K1):=by
    apply NnG.conj_mem
    apply hk
  --那么对于H中元素取共轭后，仍然在K中
  exact (to_subgroup_mem G1 K1 (h * k * h⁻¹)).mp (NnG' ↑h)

open Equiv.Perm
open Classical
abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n
def c01c23 :SymmGroup 4 :=c[0,1]*c[2,3]
def c02c13 :SymmGroup 4 :=c[0,2]*c[1,3]
def c03c12 :SymmGroup 4 :=c[0,3]*c[1,2]
def c02 :SymmGroup 4 :=c[0,2]
--H=K4，即由S4中幺元以及所有轮换型（即分解为不交轮换后，各轮换的长度）为{2，2}的元素构成的4阶子群
--（1）证明H是G的子群，简单验证即可
def H2 :Subgroup (SymmGroup 4) where
  carrier := {x:(SymmGroup 4)|x=1∨x=c01c23∨x=c02c13∨x=c03c12}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide
--（2）证明H是交换群，对每对元素验证交换律
noncomputable instance : CommGroup H2 :=by
  constructor
  rintro ⟨a,ha⟩ ⟨b,hb⟩
  --这样就化为4*4种情况来验证
  rcases ha,hb with ⟨(ha|ha|ha|ha),(hb|hb|hb|hb)⟩
  <;> simp[ha, hb] <;> try decide
  -- · simp only [ha1, hb1, Submonoid.mk_mul_mk, mul_one]
  -- · simp only [ha1, hbc01, Submonoid.mk_mul_mk, one_mul, mul_one]
  -- · simp only [ha1, hbc02, Submonoid.mk_mul_mk, one_mul, mul_one]
  -- · simp only [ha1, hbc03, Submonoid.mk_mul_mk, one_mul, mul_one]
  -- · simp only [hac01, hb1, Submonoid.mk_mul_mk, mul_one, one_mul]
  -- · simp only [hac01, hbc01, Submonoid.mk_mul_mk]
  -- · simp only [hac01, hbc02, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac01, hbc03, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac02, hb1, Submonoid.mk_mul_mk, mul_one, one_mul]
  -- · simp only [hac02, hbc01, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac02, hbc02, Submonoid.mk_mul_mk]
  -- · simp only [hac02, hbc03, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac03, hb1, Submonoid.mk_mul_mk, mul_one, one_mul]
  -- · simp only [hac03, hbc01, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac03, hbc02, Submonoid.mk_mul_mk, Subtype.mk.injEq]
  --   decide
  -- · simp only [hac03, hbc03, Submonoid.mk_mul_mk]

--（3）证明K是H的子群，如乘法封闭性可以对其中唯二元素分别验证
def K2 :Subgroup H2 where
  carrier := {x:H2|x=1∨x=c01c23}
  mul_mem' := by
    intro a b ha hb
    --乘法封闭性可以对其中唯二元素分别验证
    rcases ha with ha1|hac
    · simp only [ha1, one_mul, hb]
    · simp only [Set.mem_setOf_eq, Submonoid.coe_mul, Subgroup.coe_toSubmonoid, hac,
      mul_right_eq_self, OneMemClass.coe_eq_one]
      rcases hb with hb1|hbc
      · right
        exact hb1
      · left
        have: (a:(SymmGroup 4))*b = 1:=by
          simp only [hac, hbc]
          decide
        exact OneMemClass.coe_eq_one.mp this
  --幺元自然存在
  one_mem' := by simp only [Set.mem_setOf_eq, OneMemClass.coe_one, true_or]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, inv_eq_one, InvMemClass.coe_inv]
    --逆元也分两种情况
    rcases ha with ha1|hac
    · left
      exact ha1
    · right
      simp only [hac]
      decide
--（4）证明H是G的正规子群，这只需要对每个H中元素和S4中每个对换（因为S4由对换生成）验证即可
lemma Subgroup.K4_Normal_S4 :H2.Normal :=by
    refine { conj_mem := ?conj_mem }
    intro h hh g
    --只需要对S4中每个对换（因为S4由对换生成）验证即可，这里表现为归纳法
    induction' g using Equiv.Perm.swap_induction_on with g' x1 x2 h1n2 hg'
    · simp only [one_mul, inv_one, mul_one, hh]
      --H中的4种元素，有4种情况
    ·
      have (a: Equiv.Perm (Fin 4)) : (a * g')⁻¹ = g'⁻¹ * a⁻¹:= rfl
      show Equiv.swap x1 x2 * (g' * h * g'⁻¹) * (Equiv.swap x1 x2)⁻¹ ∈ H2
      rcases hg' with hg|hg|hg|hg
      <;> rw [hg]
      <;> unfold H2 c01c23  c02c13 c03c12
      <;> simp
      <;> fin_cases x1, x2
      <;> decide
      -- <;> unfold H2
      -- <;> unfold c01c23 c02c13 c03c12
      -- <;> fin_cases x1,x2
      -- <;> try rw [hg]
      -- · left
      --   calc
      --   _ = Equiv.swap x1 x2*(g' * h * g'⁻¹)*(Equiv.swap x1 x2)⁻¹ :=by group
      --   _ = _:=by simp only [hg1, mul_one, Equiv.swap_inv, Equiv.swap_mul_self]
      --   --对于S4中对换，又有16种情况，以下皆为验证过程
      -- · fin_cases x1,x2
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc01]
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 1 *(g'*h*g'⁻¹)*Equiv.swap 0 1:=by group
      --     _ = Equiv.swap 0 1 *c01c23*Equiv.swap 0 1 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 2 *(g'*h*g'⁻¹)*Equiv.swap 0 2:=by group
      --     _ = Equiv.swap 0 2 *c01c23*Equiv.swap 0 2 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 3 *(g'*h*g'⁻¹)*Equiv.swap 0 3:=by group
      --     _ = Equiv.swap 0 3 *c01c23*Equiv.swap 0 3 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 0 *(g'*h*g'⁻¹)*Equiv.swap 1 0:=by group
      --     _ = Equiv.swap 1 0 *c01c23*Equiv.swap 1 0 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc01]
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 2 *(g'*h*g'⁻¹)*Equiv.swap 1 2:=by group
      --     _ = Equiv.swap 1 2 *c01c23*Equiv.swap 1 2 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 3 *(g'*h*g'⁻¹)*Equiv.swap 1 3:=by group
      --     _ = Equiv.swap 1 3 *c01c23*Equiv.swap 1 3 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 0 *(g'*h*g'⁻¹)*Equiv.swap 2 0:=by group
      --     _ = Equiv.swap 2 0 *c01c23*Equiv.swap 2 0 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 1 *(g'*h*g'⁻¹)*Equiv.swap 2 1:=by group
      --     _ = Equiv.swap 2 1 *c01c23*Equiv.swap 2 1 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc01]
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 3 *(g'*h*g'⁻¹)*Equiv.swap 2 3:=by group
      --     _ = Equiv.swap 2 3 *c01c23*Equiv.swap 2 3 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 0 *(g'*h*g'⁻¹)*Equiv.swap 3 0:=by group
      --     _ = Equiv.swap 3 0 *c01c23*Equiv.swap 3 0 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 1 *(g'*h*g'⁻¹)*Equiv.swap 3 1:=by group
      --     _ = Equiv.swap 3  1*c01c23*Equiv.swap  3 1:=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap  3 2*(g'*h*g'⁻¹)*Equiv.swap 3 2:=by group
      --     _ = Equiv.swap 3 2 *c01c23*Equiv.swap 3 2 :=by simp only [Fin.isValue, hgc01]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc01]

      -- · fin_cases x1,x2
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc02]
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 1 *(g'*h*g'⁻¹)*Equiv.swap 0 1:=by group
      --     _ = Equiv.swap 0 1 *c02c13*Equiv.swap 0 1 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 2 *(g'*h*g'⁻¹)*Equiv.swap 0 2:=by group
      --     _ = Equiv.swap 0 2 *c02c13*Equiv.swap 0 2 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 3 *(g'*h*g'⁻¹)*Equiv.swap 0 3:=by group
      --     _ = Equiv.swap 0 3 *c02c13*Equiv.swap 0 3 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 0 *(g'*h*g'⁻¹)*Equiv.swap 1 0:=by group
      --     _ = Equiv.swap 1 0 *c02c13*Equiv.swap 1 0 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc02]
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 2 *(g'*h*g'⁻¹)*Equiv.swap 1 2:=by group
      --     _ = Equiv.swap 1 2 *c02c13*Equiv.swap 1 2 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 3 *(g'*h*g'⁻¹)*Equiv.swap 1 3:=by group
      --     _ = Equiv.swap 1 3 *c02c13*Equiv.swap 1 3 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 0 *(g'*h*g'⁻¹)*Equiv.swap 2 0:=by group
      --     _ = Equiv.swap 2 0 *c02c13*Equiv.swap 2 0 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 1 *(g'*h*g'⁻¹)*Equiv.swap 2 1:=by group
      --     _ = Equiv.swap 2 1 *c02c13*Equiv.swap 2 1 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc02]
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 3 *(g'*h*g'⁻¹)*Equiv.swap 2 3:=by group
      --     _ = Equiv.swap 2 3 *c02c13*Equiv.swap 2 3 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 0 *(g'*h*g'⁻¹)*Equiv.swap 3 0:=by group
      --     _ = Equiv.swap 3 0 *c02c13*Equiv.swap 3 0 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 1 *(g'*h*g'⁻¹)*Equiv.swap 3 1:=by group
      --     _ = Equiv.swap 3  1*c02c13*Equiv.swap  3 1:=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap  3 2*(g'*h*g'⁻¹)*Equiv.swap 3 2:=by group
      --     _ = Equiv.swap 3 2 *c02c13*Equiv.swap 3 2 :=by simp only [Fin.isValue, hgc02]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc02]

      -- · fin_cases x1,x2
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc03]
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 1 *(g'*h*g'⁻¹)*Equiv.swap 0 1:=by group
      --     _ = Equiv.swap 0 1 *c03c12*Equiv.swap 0 1 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 2 *(g'*h*g'⁻¹)*Equiv.swap 0 2:=by group
      --     _ = Equiv.swap 0 2 *c03c12*Equiv.swap 0 2 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 0 3 *(g'*h*g'⁻¹)*Equiv.swap 0 3:=by group
      --     _ = Equiv.swap 0 3 *c03c12*Equiv.swap 0 3 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 0 *(g'*h*g'⁻¹)*Equiv.swap 1 0:=by group
      --     _ = Equiv.swap 1 0 *c03c12*Equiv.swap 1 0 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc03]
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 2 *(g'*h*g'⁻¹)*Equiv.swap 1 2:=by group
      --     _ = Equiv.swap 1 2 *c03c12*Equiv.swap 1 2 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 1 3 *(g'*h*g'⁻¹)*Equiv.swap 1 3:=by group
      --     _ = Equiv.swap 1 3 *c03c12*Equiv.swap 1 3 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 0 *(g'*h*g'⁻¹)*Equiv.swap 2 0:=by group
      --     _ = Equiv.swap 2 0 *c03c12*Equiv.swap 2 0 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 1 *(g'*h*g'⁻¹)*Equiv.swap 2 1:=by group
      --     _ = Equiv.swap 2 1 *c03c12*Equiv.swap 2 1 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc03]
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 2 3 *(g'*h*g'⁻¹)*Equiv.swap 2 3:=by group
      --     _ = Equiv.swap 2 3 *c03c12*Equiv.swap 2 3 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 0 *(g'*h*g'⁻¹)*Equiv.swap 3 0:=by group
      --     _ = Equiv.swap 3 0 *c03c12*Equiv.swap 3 0 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap 3 1 *(g'*h*g'⁻¹)*Equiv.swap 3 1:=by group
      --     _ = Equiv.swap 3  1*c03c12*Equiv.swap  3 1:=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;left
      --     simp only [Fin.zero_eta, Fin.isValue, Fin.reduceFinMk, mul_inv_rev, Equiv.swap_inv]
      --     calc
      --     _ = Equiv.swap  3 2*(g'*h*g'⁻¹)*Equiv.swap 3 2:=by group
      --     _ = Equiv.swap 3 2 *c03c12*Equiv.swap 3 2 :=by simp only [Fin.isValue, hgc03]
      --     _ = _ :=by decide
      --   · right;right;right
      --     simp only [Fin.zero_eta, Fin.isValue, Equiv.swap_self, refl_mul, hgc03]

--（5）证明K是H的正规子群，直接使用交换群的子群皆正规的结论
lemma Subgroup.Z2_Normal_K4 : K2.Normal :=by exact Subgroup.normal_of_comm K2
--（6）证明K不是G的正规子群
lemma Subgroup.Z2_not_Normal_S4 :¬ (to_subgroup (SymmGroup 4) K2).Normal :=by
  --用反证法
  intro hn
  --化简正规性条件
  have hn':∀k∈to_subgroup (SymmGroup 4) K2,∀(g : SymmGroup 4),
       g*k*g⁻¹∈to_subgroup (SymmGroup 4) K2:= by apply hn.conj_mem
  --证明(0,1)(2,3)在H中
  have hc01inH:c01c23∈H2:=by right;left;rfl
  --证明(0,1)(2,3)在K中
  have hc01inK:⟨c01c23,hc01inH⟩∈K2:=by right;rfl
  have hc01inK':c01c23∈to_subgroup (SymmGroup 4) K2 :=by
    simp[← to_subgroup_mem ] at hc01inK
    exact hc01inK
  --再次化简正规性条件，取K中元素(0,1)(2,3)，G中元素(0,2)
  let hn'':=hn' c01c23 hc01inK' c02
  --计算(0,2)(0,1)(2,3)(0,2)=(0,3)(1,2)
  have ca:c02 * c01c23 * c02⁻¹=c03c12:=by decide
  simp only [ca] at hn''
  --证明(0,3)(1,2)在H中
  have hc03inH:c03c12∈H2:=by right;right;right;rfl
  --证明(0,3)(1,2)不在K中
  have hc03ninK:⟨c03c12,hc03inH⟩∉K2:=by
    intro hc03
    --直接验证(0,3)(1,2)不是K中的唯二元素
    rcases hc03 with hc031|hc03c01
    · simp only [Submonoid.mk_eq_one] at hc031
      contrapose! hc031
      decide
    · simp only [Submonoid.mk_eq_one] at hc03c01
      contrapose! hc03c01
      decide
  have hc03ninK':c03c12∉to_subgroup (SymmGroup 4) K2 :=by
    intro hc03inK'
    contrapose! hc03ninK
    simp[← to_subgroup_mem]
    exact hc03inK'
  --正规性条件表明(0,3)(1,2)在K中，但是(0,3)(1,2)不在K中，矛盾
  tauto

--找到反例
theorem Subgroup.Normal_not_trans:
  H2.Normal∧K2.Normal∧¬ (to_subgroup (SymmGroup 4) K2).Normal:=by
  constructor
  · exact K4_Normal_S4
  constructor
  · exact Z2_Normal_K4
  · exact Z2_not_Normal_S4

end Exercise_234
