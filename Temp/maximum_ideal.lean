--这不是我正式提交这项作业，只是麻烦助教帮我看看我的这项作业哪里有问题，具体哪里需要改的。助教您可以在提出修改意见后将作业打回方便我自己修
--改后再次提交。
--完成这项作业时我完全仿照了C03_05_Basic_Things_in_Abstract_Algebra文件中S02的theorem eqord的证明，但在引理h1和h2的"simp"前面"\."位
--置仍然出现了报错，最后一行也出现了报错。
import Mathlib.Algebra.Ring.Defs
import MIL.Common
import Mathlib.Tactic

example {G : Type*} [Group G] (a b : G) : orderOf a = orderOf (b * a * b⁻¹) := by
  have h1: ∀ k : ℕ , (b * a * b⁻¹) ^ k = b * a ^ k * b⁻¹ := by
    intro k
    induction' k with k ih
    · simp only [pow_zero, mul_one, one_mul]
    · calc
        _ = (b * a * b⁻¹) ^ k * (b * a * b⁻¹) := by rw [pow_succ (b * a * b⁻¹) k]; group
        _ = b * a ^ k * b⁻¹ * (b * a * b⁻¹) := by rw[ih]; group
        _ = b * a ^ k * a * b⁻¹ := by group
        _ = _ := by rw [pow_succ a k]; group
  have h2: ∀ k : ℕ , (b⁻¹ * (b * a * b⁻¹) * b) ^ k = b⁻¹ * (b * a * b⁻¹) ^ k * b := by
    intro k
    induction' k with k ih
    · simp only [pow_zero, mul_one, one_mul]
    · calc
        _ = (b⁻¹ * (b * a * b⁻¹) * b) ^ k * (b⁻¹ * (b * a * b⁻¹) * b) := by rw [pow_succ (b⁻¹ * (b * a * b⁻¹) * b) k]; group
        _ = b⁻¹ * (b * a * b⁻¹) ^ k * b * (b⁻¹ * (b * a * b⁻¹) * b) := by rw[ih]; group
        _ = b⁻¹ * (b * a * b⁻¹) ^ k * (b * a * b⁻¹) * b := by group
        _ = _ := by rw [pow_succ (b * a * b⁻¹) k]; group
  have div1: orderOf (b * a * b⁻¹) ∣ orderOf a := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = b * a ^ (orderOf a) * b⁻¹ := by rw [h1 (orderOf a)]
      _ = b * 1 * b⁻¹ := by rw [pow_orderOf_eq_one a]
      _ = 1 := by group
  have div2: orderOf a ∣ orderOf (b * a * b⁻¹) := by
    apply orderOf_dvd_of_pow_eq_one
    calc
      _ = (b⁻¹ * (b * a * b⁻¹) * b) ^ orderOf (b * a * b⁻¹) := by group
      _ = b⁻¹ * (b * a * b⁻¹) ^ (orderOf (b * a * b⁻¹)) * b := by rw [h2 (orderOf (b * a * b⁻¹))];group
      _ = b⁻¹ * 1 * b := by rw [pow_orderOf_eq_one (b * a * b⁻¹)]; group
      _ = 1 := by group
  apply Nat.dvd_antisymm div1 div2
