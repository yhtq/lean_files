import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

theorem self_inverse {G : Type} [Group G] (g : G) (h : g^2 = 1) : g = g⁻¹ := by
  calc g = 1 * g     := by rw [one_mul g]
       _ = 1 ⁻¹ * g  := by simp only [one_mul, inv_one]
       _ = (g^2)⁻¹ * g := by rw [h]
       _ = (g * g)⁻¹ * g := by simp only [pow_succ, pow_zero, one_mul, mul_inv_rev,
         inv_mul_cancel_right]
       _ = g ⁻¹ * g⁻¹ * g := by rw [←mul_inv_rev]
       _ = g⁻¹ * (g⁻¹ * g) := by rw [mul_assoc]
       _ = g⁻¹ * 1       := by simp only [mul_left_inv, mul_one]
       _ = g⁻¹           := by rw [mul_one]
