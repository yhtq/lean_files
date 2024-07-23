import Mathlib.Tactic

section E_1685
-- open scoped Classical
-- open Subgroup

example : Prop -> Prop := by sorry
example (x: Nat): PProd Nat (x > 1) := sorry
example : (x: Nat) ×' (x > 1) := by sorry

lemma nzpow_mul.{u_1} {α : Type u_1} [DivisionMonoid α] (a : α) (m: ℕ): ∀ n : ℤ, a ^ (m * n) = (a ^ m) ^ n
-- we can calcular and rewrite by using this lemma more easily
  | (n : ℕ) => by
    simp only [zpow_natCast]
    rw [(pow_mul a m n).symm]
    rw [←zpow_natCast]
    simp only [Nat.cast_mul]
  | .negSucc n => by
    simp only [Int.ofNat_mul_negSucc, Nat.succ_eq_add_one, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      zpow_neg, zpow_negSucc, inv_inj]
    rw [(pow_mul a m (n+1)).symm]
    rw [←zpow_natCast]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

example {G: Type*} [Group G](H K : Subgroup G) (g : G) (m n : ℕ )(hpos: 0 < m * n )(hord : orderOf g = m * n )(hcyc :  ∀ (x : G), x ∈ zpowers g) (hmn : Nat.Coprime m n)
: G ≃* (zpowers (g ^ m) × zpowers (g ^ n)) where
-- 1. In order to prove that $G\cong \left \langle a^{m}  \right \rangle \times \left \langle a^{n}  \right \rangle$ , we can define an isomorphism between them.
  toFun := by
   intro x
   let k := Classical.choose (Subgroup.mem_zpowers_iff.mp (hcyc x))
   let s := Nat.gcdA m n
   let t := Nat.gcdB m n
   --2. Thanks to the Bezout, we can get that $\exist \ s\  t, s \times m + t \times n =1$
   --, so, for$\ \forall g \in G, g=g^1=g^{s \times m + t \times n}= g^{s \times m} \times g^{t \times n}$.
   --we can find $g^{s \times m} \in \left \langle a^{m}  \right \rangle, g^{t \times n} \in \left \langle a^{n}  \right \rangle $,
   --which can turn into an isomorphism between them.
   constructor
   · use x ^ (m * s)
     apply Subgroup.mem_zpowers_iff.mpr
     use k * s
     calc
       _= g ^ (m * k * s):=by rw[mul_assoc,nzpow_mul g m (k * s) ]
       _= (g ^ k)^ (m * s):= by
         nth_rw 2 [mul_comm]
         rw[mul_assoc,zpow_mul g k (m * s)]
       _= _ := by rw[ Classical.choose_spec (Subgroup.mem_zpowers_iff.mp (hcyc x))]

   · use x ^ (n * t)
     apply Subgroup.mem_zpowers_iff.mpr
     use k * t
     calc
       _= g ^ (n * k * t):=by rw[mul_assoc,nzpow_mul g n (k * t) ]
       _= (g ^ k)^ (n * t):= by
         nth_rw 2 [mul_comm]
         rw[mul_assoc,zpow_mul g k (n * t)]
       _= _ := by rw[ Classical.choose_spec (Subgroup.mem_zpowers_iff.mp (hcyc x))]
-- 3. We can easily find a inv_fun by $(a, b)\longmapsto ab$
  invFun := by
    intro ⟨xh, xk⟩
    use xh * xk


--4. We should verify the left_inv
  left_inv := by
    intro x
    let s := Nat.gcdA m n
    let t := Nat.gcdB m n
    show x ^ (m * s) * x ^ (n * t) = x
    rw[← zpow_add]
    have : m * s + n * t = 1 :=by
      unfold Nat.Coprime at hmn
      show m * (Nat.gcdA m n) + n *(Nat.gcdB m n)= 1
      rw[← Nat.gcd_eq_gcd_ab m n]
      rw[hmn]
      simp only [Nat.cast_one]
    rw[this, zpow_one]
--5. We should verify the right_inv
  right_inv := by
    intro x
    let s := Nat.gcdA m n
    let t := Nat.gcdB m n
    let hk := x.1.val * x.2.val
    let pnh := Classical.choose (Subgroup.mem_zpowers_iff.mp x.1.property)
    let pnk := Classical.choose (Subgroup.mem_zpowers_iff.mp x.2.property)
    let qph := Classical.choose_spec (Subgroup.mem_zpowers_iff.mp x.1.property)
    let qpk := Classical.choose_spec (Subgroup.mem_zpowers_iff.mp x.2.property)
    have bezout: m * s + n * t = 1 :=by
      unfold Nat.Coprime at hmn
      show m * (Nat.gcdA m n) + n *(Nat.gcdB m n)= 1
      rw[← Nat.gcd_eq_gcd_ab m n]
      rw[hmn]
      simp only [Nat.cast_one]
    have bezout1 : m * s = 1 - n * t :=by
      rw[← bezout]
      ring_nf
    have bezout2 : n * t = 1 - m * s :=by
      rw[← bezout]
      ring_nf
    rw[orderOf_eq_iff hpos] at hord
    rcases hord with ⟨hgn, __⟩
    have nh : hk ^ (m * s)= x.1 :=by
      rw [← qph]
      show (x.1.val * x.2.val) ^ (m * s) = (g ^ m) ^ pnh
      rw [← qph,← qpk]
      show ((g ^ m) ^ pnh * (g ^ n) ^ pnk) ^ (m * s) = (g ^ m) ^ pnh
      calc
       _= g ^ (m * pnh * (m * s)) * g ^ (n * m *(pnk * s)) :=by
         rw [← nzpow_mul,← nzpow_mul,← zpow_add,← zpow_add,← zpow_mul]
         ring_nf
       _= g ^ (m * pnh)* g ^ (m * n *(pnk * s - pnh * t)) :=by
         rw [bezout1, ←zpow_add, ← zpow_add]
         ring_nf
       _=_ := by
         nth_rw 2 [zpow_mul]
         rw [pow_mul,← zpow_natCast, ←zpow_natCast, ←zpow_mul]at hgn
         rw[hgn, one_zpow, mul_one, nzpow_mul]
    have nk : hk ^ (n * t) = x.2 :=by
      rw [← qpk]
      show (x.1.val * x.2.val) ^ (n * t) = (g ^ n) ^ pnk
      rw [← qph,← qpk]
      show ((g ^ m) ^ pnh * (g ^ n) ^ pnk) ^ (n * t) = (g ^ n) ^ pnk
      calc
       _= g ^ (n * pnk * (n * t)) * g ^ (m * n *(pnh * t)) :=by
         rw [← nzpow_mul,← nzpow_mul,← zpow_add,← zpow_add,← zpow_mul]
         ring_nf
       _= g ^ (n * pnk)* g ^ (n * m *(pnh * t - pnk * s)) :=by
         rw [bezout2, ←zpow_add, ← zpow_add]
         ring_nf
       _=_ := by
         nth_rw 2 [zpow_mul]
         rw [pow_mul,← zpow_natCast, ←zpow_natCast, ←zpow_mul,mul_comm]at hgn
         rw[hgn, one_zpow, mul_one, nzpow_mul]
    dsimp
    ext
    · exact nh
    · exact nk

--6. We should verify the function fit the law in groups
  map_mul' := by
   intro x y
   let s := Nat.gcdA m n
   let t := Nat.gcdB m n
   let kx := Classical.choose (Subgroup.mem_zpowers_iff.mp (hcyc x))
   let ky := Classical.choose (Subgroup.mem_zpowers_iff.mp (hcyc y))
   let hkx := Classical.choose_spec (Subgroup.mem_zpowers_iff.mp (hcyc x))
   let hky := Classical.choose_spec (Subgroup.mem_zpowers_iff.mp (hcyc y))
   have hl : (x * y) ^ (m * s) = x ^ (m * s) * y ^ (m * s) :=by
     rw[←hkx, ←hky]
     show (g ^ kx * g ^ ky) ^ (m * s)=(g ^ kx) ^ (m * s) * (g ^ ky) ^ (m * s)
     rw[← zpow_mul,← zpow_mul,← zpow_add,← zpow_add,← zpow_mul]
     ring_nf
   have hr : (x * y) ^ (n * t) = x ^ (n * t) * y ^ (n * t) :=by
     rw[←hkx, ←hky]
     show (g ^ kx * g ^ ky) ^ (n * t)=(g ^ kx) ^ (n * t) * (g ^ ky) ^ (n * t)
     rw[← zpow_mul,← zpow_mul,← zpow_add,← zpow_add,← zpow_mul]
     ring_nf
   dsimp
   ext
   · exact hl
   · exact hr

end E_1685
