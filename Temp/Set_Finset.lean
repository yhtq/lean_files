import Mathlib.Data.Finset.Basic
import Mathlib.Init.Set
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Card
-- 子类型
  -- 在 Lean 中，为了方便起见引入了子类型的概念，子类型的对象可以自动的转换为原来的类型，而原类型的对象附加一个证明就是子类型的对象。一般的，子类型的定义类似于：
  structure subtype {α : Sort u} (p : α → Prop) where
    val : α
    property : p val
  -- 在 Lean 中可以简写为 {x // p x}，其中 x 是 val 的别名。
  -- 典型例子是 Fin n，它相当于 {val : ℕ // val < n} ，也即：

  structure fin_n (n: ℕ) where
    val : ℕ
    isLt : val < n

  example (n: Fin 10) : n.val < 10 := n.isLt
  example (n: Fin 10) : (↑n) < (10: ℕ) := n.isLt
  -- 上面这些定理在 Lean 中是完全相同的，只是进行了一些类型转换而已。

  def fin_to_N : Fin 10 → ℕ := fun n => n.val


  def N_to_fin : (n: ℕ) -> (p: n < 10) -> Fin 10 := fun n p => {val := n, isLt := p}
  def N_to_fin' : (n: ℕ) -> (p: n < 10) -> Fin 10 := fun n p => ⟨n, p⟩
  -- 上面两个定理也是相同定理的不同表述

  -- 为了方便起见，Set 可以直接转换称类型，例如：
  def set_fin_10 : Set ℕ := {x | x < 10}
  -- Set.univ 表示某个类型对应的全集
  def set_fin_10' : Set (Fin 10) := Set.univ
  def N_to_fin'' : (n: ℕ) -> (p: n ∈ set_fin_10) -> Fin 10 := sorry

  def x_5' : set_fin_10 := ⟨5, by
                                unfold set_fin_10
                                simp only [Set.mem_setOf_eq, Nat.reduceLT]
                                ⟩
  #check x_5'
  -- 可以看到 set_fin_10 被自动转换成了一个类型，这个类型实际上就是 {x : ℕ // x ∈ set_fin_10}，处理方法也是完全一样的
  -- 考虑下面的函数如何定义？
  def N_in_set_to_fin : (n: set_fin_10) -> Fin 10 := sorry
  -- （其实这俩类型 exactly 是一个类型，只是大家让大家自己试试拆开和组合）

-- 其他有限类型
  -- Lean 中有非常多关于有限类型的描述，包括：
    -- Fin n: 就是上面介绍的 {val : ℕ // val < n}，表示小于 n 的自然数，常常作为下标的类型
    -- Fintype α: 这是一个 type class，表示类型 α 是有限的并且是由某种 decidable 命题构造得到。具体的实现是一个 Finset 上的类型
    -- Finite α: 同样是一个 type class，表示类型 α 是有限的，但是不要求 decidable，具体的实现是存在一个 Fin n 到 α 的一一映射
      #check Fintype.ofFinite
      -- 请注意上面的 def 被标注了 noncomputable，这是必要的，应用该 def 的时候也必须标注 noncomputable。
      -- 原则上，除非非常清楚自己需要 decidable 进行计算，否则不建议使用 Fintype
    def finite_to_fintype {α: Type} [Fintype α] : Finite α := inferInstance
    -- 这里 inferInstace 是可以直接被 Instance 系统推算得到的意思，实际应用时是自动匹配的，不需要手工写
    -- 下面的定义是失败的
    -- def fintype_to_finite {α: Type} [Finite α] : Fintype α := inferInstance
    noncomputable def fintype_to_finite {α: Type} [Fintype α] : Finite α := inferInstance

-- 集合与列表
  -- 集合的实际应应该在后面还会有介绍，这里只是稍微提几句，主要是解释清楚如何描述有限性。
  -- 众所周知 Lean 是一种函数式语言，集合并不如同在通常的数学语言中那样成为一个基本概念。一个 Set α 被实现为一个函数 α → Prop，表示一个元素是否在集合中。
  -- 与之相对的，列表是经典函数式编程的概念，它被实现为一个递归类型。从表现来看，List α 就是有限，有序的一列 α 类型的元素。
  -- 非常神秘的事情是，Lean 中定义了 Multiset，它是 List 商掉置换（也就是无序列表）。更加神秘的是，Lean 中定义了 Finset，它是 Multiset 商掉重复元素（也就是无序无重列表）。而另一方面，一个集合 (s: Set α) 通过 Set.Finite 定义了有限性，实现为当且仅当它对应的类型是 Finite 的（注意不是 Fintype）。这就导致 Finite 的 Set 未必是 Finset，除非你添加 noncomputable 的标注或者索性直接 open Classical。

-- 子群
  variable {G : Type} [Group G]
  -- 如上面 variable 所示，我们用类型 instance 表示 G 是一个群，如何表示 H 是 G 的子群呢？在 Lean 中子群的实现有些讨巧：
    -- 首先，Subgroup G 是一个类型，它的对象是 G 中的子群，定义类似于：
      structure subgroup' {α : Sort u} (p : α → Prop) where
        carrier : Set G
        mul_mem' : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
        one_mem' : 1 ∈ carrier
        inv_mem' : ∀ {x : G}, x ∈ carrier → x⁻¹ ∈ carrier
        -- ...... 以及结合律等等命题
      -- 也就是一个 G 上的集合配上子群需要的性质
    -- 其次，对于任意的 Subgroup G 中的元素 h，h 可以像上面的集合一样，自动转换为一个类型，且这个类型是一个群
    def subgroup_is_group (h: Subgroup G) : Group h := inferInstance
    -- 这个类型是如上所述的 G 的子类型，许多群上的 instance 会自动推导到子群上，例如：
    def subgroup_of_finite_group_is_finite (h: Subgroup G) [Finite G] : Finite h := inferInstance
    -- 这里不写 DecidablePred 是无法推导的
    def subgroup_of_fintype_group_is_fintype (h: Subgroup G) [Fintype G] [DecidablePred (fun a => a ∈ h)] : Fintype h := inferInstance

    -- 下面的定理自动地运用了子群上的 Group Instance
    #check mul_right_inv
    def mul_right_inv_on_subgroup (h: Subgroup G) (a: h)  := mul_right_inv a
    #check mul_right_inv_on_subgroup

    -- 显然，我们理解的子群应该成为某种集合的延伸，包括一个 G 中的元素应该可以判断属不属于 h，两个子群相等当且仅当具有相同的元素等等。类似这些命题被统一实现为一个 typeclass SetLike，简单来说就是一个 SetLike 的类型可以自动转换为一个集合，且相等当且仅当转换出的集合相等
    #check SetLike.coe_set_eq
    example (h k: Subgroup G) :  h.carrier = k.carrier ↔ h = k := by
      let set_like_coe :=  @SetLike.coe_set_eq  _ _ _ h k
      unfold SetLike.coe at set_like_coe
      unfold Subgroup.instSetLike at set_like_coe
      simp at set_like_coe
      exact set_like_coe
    #check SetLike.ext_iff
    def test (h: Subgroup G) :=  SubgroupClass.toGroup h
    example (h k: Subgroup G) : h = k ↔ (∀ x: G, x ∈ h ↔ x ∈ k) := SetLike.ext_iff
    #check Subgroup.ext
    -- 一般的，SetLike （包括子群）上定义了典范的序关系，构成了一个偏序集 （这在 Lean 中也是一个 typeclass）。同时，当然有最大的子群和最小的子群。你并不能在 Lean 中说一个子群 h = G，既然 G 具有类型 Type 而 h 具有类型 Subgroup G，为了起到替代作用， Subgroup G 上定义了最大元 ⊤ (\top) 和最小元 ⊥ (\bot)，并且有：
    #check (⊤: Subgroup G)
    #check Subgroup.coe_top
    -- 同时，交运算（既然两个子群的交仍是子群）被定义为 h ⊓ k 或者说两个元素的下确界 inf，而上确界 h ⊔ k 当然是包含 h 和 k 的最小的子群。
    #check Subgroup.coe_inf
    -- 这些性质统合起来，被实现为了一个 CompleteLattice，不再赘述
-- 一些习题
  -- 1. 通过补全 sorry，证明下面定义的运算构成群
      def mul_Z_n (n: ℕ) (a b: Fin n) : Fin n := ⟨(a.val + b.val) % n, by
        sorry⟩
      instance is_group (n: ℕ) (p: n > 0): Group (Fin n) where
        mul (a b: Fin n) := ⟨(a.val + b.val) % n, by
                exact Nat.mod_lt (↑a + ↑b) p⟩
        mul_assoc := sorry
        one := ⟨0, by sorry⟩
        one_mul := sorry
        mul_one := sorry
        inv (a: Fin n) := ⟨n - a.val, by sorry⟩
        mul_left_inv := sorry
        div (a b: Fin n) :=  ⟨(a.val + (n - b.val)) % n, by sorry⟩

  -- 2. 用定义验证：
      def inv_in_subgroup (h: Subgroup G) (a: h) : ∃a_inv: h, (a_inv: G) * (a: G) = 1 := sorry
  -- 3. 证明子群的交还是子群
      def subgroup_inter_is_subgroup (h k: Subgroup G) : ∃ (i: Subgroup G), (i.carrier = h.carrier ∩ k.carrier) := sorry
  -- 4. 证明 a H a⁻¹ 是 H 的子群
      def conjugate_subgroup (a: G) (H: Subgroup G) : ∃ (i: Subgroup G), (i.carrier = {a * h * a⁻¹ | h: H }) := sorry
  -- 5. 对于 G 中任意元素 a，显式构造由其生成的最小子群
  -- 6. 下面给出了群元素阶的可计算定义，请补全 sorry
      def orderOf' [Fintype G][DecidableEq G] (a: G) := List.head (List.dropWhile (fun n => a ^ n ≠ 1 ∨ n = 0 ) (List.range (Fintype.card G + 1))) (by sorry)
      theorem orderOf'_correct [Fintype G][DecidableEq G] (a: G) : orderOf a = orderOf' a := sorry

      instance Z_42_is_group : Group (Fin 42) := is_group 42 (by norm_num)

      #eval orderOf' (4: Fin 42)
      #eval Finset.filter (fun n => orderOf' n = 42) (Finset.univ: Finset (Fin 42))
      -- 你应该可以看到 Z_42 的所有生成元，这体现了 Finset 的优越性（上面的计算写成 Set 是无法完成的）
      example : {1, 5, 11, 13, 17, 19, 23, 25, 29, 31, 37, 41} = {x: Fin 42 | @orderOf (Fin 42) DivInvMonoid.toMonoid x = 42} := by
        -- 上面手动指定 orderOf 使用的 instance 是因为 Fin 42 上本身有 instance，不指定的话会导致找到默认的而不是我们想要的（上面定义的）instance
        simp only [orderOf'_correct]
        simp only [Fin.isValue]
        apply Set.toFinset_inj.mp -- 如果没有用这个将 Set 转换为 Finset，将是无法使用 decide 完成证明的
        decide
@[ext]
structure point where
  x: ℕ
  y: ℕ
  h: 2 ∣ x + y
