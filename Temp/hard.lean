/-  --Special Ex 070401
Let M and N be normal subgroups of the group G.
If M ∩ N = 1, then for any a ∈  M and b ∈ N, we have ab = ba.
-/
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
open Subgroup Complex

variable {θ : ℝ}
lemma I_pow (n: Nat) : I ^ n = match n % 4 with
  | 0 => 1
  | 1 => I
  | 2 => -1
  | 3 => -I
  | _ => 1
  := by
        have : n = 4 * (n / 4) + n % 4 := Eq.symm (Nat.div_add_mod n 4)
        nth_rw 1 [this]
        rw [pow_add, pow_mul, I_pow_four]
        simp
        have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
        have : n % 4 ∈ ({0, 1, 2, 3}: Finset ℕ) := by show n % 4 ∈ Finset.range 4; simp [this]
        simp at this
        rcases this with h | h | h | h <;> rw [h] <;> norm_num
        rw [((by norm_num): 3 = 1 + 2)]
        rw [pow_add]
        simp

example  : Real.cos (3 * θ) = 4 * (Real.cos θ) ^ 3 - 3 * Real.cos θ := by
  --By Euler's formula, it follows that $e^{i θ}=cos θ+i sin θ$
--   have theta : _ := Complex.exp_mul_I θ
  have (x: ℝ) : Real.cos x = ((cexp (x * I) + cexp (- x * I))/2).re := by
        have : - (x: ℂ) = ↑(-x) := by simp
        --rw [this]
        rw [Complex.exp_mul_I x, Complex.exp_mul_I (-x)]
        simp
        rw [cos_ofReal_re]
  have im_zero (x: ℝ) : ((cexp (x * I) + cexp (- x * I))/2).im = 0 := by
        have : - (x: ℂ) = ↑(-x) := by simp
        --rw [this]
        rw [Complex.exp_mul_I x, Complex.exp_mul_I (-x)]
        simp
  have re_pow (c: ℂ) (n: ℕ): c.im = 0 -> (c^n).re = (c.re)^n := by
    intro h
    have : c = c.re := Complex.ext rfl h
    nth_rw 1 [this]
    rw [<-ofReal_pow, ofReal_re]
  repeat rw [this]
  rw [<-re_pow _ _ (im_zero θ)]
  repeat rw [<-re_ofReal_mul]
  rw [<-sub_re]
  apply congr_arg
  field_simp
  ring_nf
  repeat rw [<-exp_nat_mul]
  push_cast
  rw [mul_comm 3, mul_neg 3, mul_comm 3, <-exp_add, <-exp_add]
  ring_nf


--   --By calculation, it is found that $e^{i θ}^2= cos^2 θ - i sin^2 θ + 2 i cos θ * sin θ$
--   have thete_pow_two : (Complex.exp (θ * Complex.I)) ^ 2 = ((Complex.cos θ) ^ 2 - (Complex.sin θ) ^ 2) + 2 * Complex.sin θ * Complex.cos θ * Complex.I  := by
--     rw [theta, sq]
--     ring
--     simp [Complex.I_mul_I]
--     ring
--   --By calculation, it is found that $e^{i θ}^3=4 cos^3 θ - 3 cos θ + i (3 sin θ  - 4 sin^3 θ )$
--   have thete_pow_three : (Complex.exp (θ * Complex.I)) ^ 3 = (4 * Complex.cos θ ^ 3 - 3 * Complex.cos θ) + (3 * Complex.sin θ - 4 * Complex.sin θ ^ 3 ) * Complex.I := by
--     nth_rw 1 [(by norm_num : 3 = 1 + 2)]
--     ring
--     rw [Complex.exp_mul_I]
--     ring
--     rw [(by sorry: Complex.I ^3 = Complex.I * Complex.I * Complex.I), (by norm_num: Complex.I ^2 = Complex.I * Complex.I), ]
-- --
-- --   calc
-- --       _ = (Complex.exp (θ * Complex.I)) ^ 1 * (Complex.exp (θ * Complex.I)) ^ 2 := by rw[pow_add]
-- --       _ = (Complex.cos θ + Complex.sin θ * Complex.I) * (((Complex.cos θ) ^ 2 - (Complex.sin θ) ^ 2) + 2 * Complex.sin θ * Complex.cos θ * Complex.I) := by rw[pow_one, thete_pow_two, theta]
-- --       _ = (Complex.cos θ) ^ 3 - Complex.cos θ * (Complex.sin θ) ^ 2 + 2 * (Complex.cos θ) ^ 2 * Complex.sin θ *  Complex.I + Complex.sin θ  * (Complex.cos θ) ^ 2 * Complex.I - (Complex.sin θ) ^ 3 * Complex.I + 2 * (Complex.sin θ) ^ 2 * Complex.cos θ * (Complex.I * Complex.I) := by ring
-- --       _ = (Complex.cos θ) ^ 3 - Complex.cos θ * (Complex.sin θ) ^ 2 + 2 * (Complex.cos θ) ^ 2 * Complex.sin θ *  Complex.I + Complex.sin θ  * (Complex.cos θ) ^ 2 * Complex.I - (Complex.sin θ) ^ 3 * Complex.I + 2 * (Complex.sin θ) ^ 2 * Complex.cos θ * (-1) := by rw [Complex.I_mul_I]
-- --       _ = (Complex.cos θ) ^ 3 - 3 * (Complex.cos θ) * (Complex.sin θ) ^ 2 + Complex.I * (3 * (Complex.cos θ) ^ 2 * (Complex.sin θ) - (Complex.sin θ) ^ 3) := by ring
-- --       _ = (Complex.cos θ) ^ 3 - 3 * (Complex.cos θ) * (1 - (Complex.cos θ) ^ 2) + Complex.I * (3 * (1 - (Complex.sin θ) ^ 2) * (Complex.sin θ) - (Complex.sin θ) ^ 3) := by nth_rw 1 [Complex.cos_sq' θ, Complex.sin_sq θ]
-- --       _ = _ := by ring
--   --By Euler's formula, it follows that $e^{i θ}^3= e^{i 3 θ}=cos 3 θ+i sin 3 θ$
--   have thete_pow_three' : Complex.exp (↑θ * Complex.I) ^ 3 = Complex.cos (3 * θ) + Complex.sin (3 * θ) * Complex.I := by rw [theta, (Complex.cos_add_sin_mul_I_pow 3 θ)]; rfl
--   --By $e^{i θ}^3= cos 3 θ+i sin 3 θ$, it follows that $Re(e^{i θ}^3)= cos 3 θ$
--   have costhree: (Complex.exp (3 * θ * Complex.I)).re = Real.cos (3 * θ) := by
--     simp [Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
--     have : Complex.cos (3 * θ) = Real.cos (3 * θ) := by simp only [Complex.ofReal_cos,
--       Complex.ofReal_mul, Complex.ofReal_ofNat]
--     rw [this]
--     have : Complex.sin (3 * θ) = Real.sin (3 * θ)  := by simp only [Complex.ofReal_sin,
--       Complex.ofReal_mul, Complex.ofReal_ofNat]
--     rw [this]
--     rw [Complex.ofReal_re, Complex.ofReal_im]
--     ring
--   -- Re(cos θ) = cos θ
--   have c_re: (Complex.cos θ ).re = Real.cos θ  := by rfl
--   -- Im(cos θ) = 0
--   have c_im: (Complex.cos θ ).im = 0  := by exact Complex.cos_ofReal_im θ
--   -- Re(cos θ^2) = cos θ^2
--   have c2_re: (Complex.cos θ ^ 2 ).re = Real.cos θ ^ 2  := by
--     nth_rw 1 [(by norm_num : 2 = 1 + 1), pow_add, pow_one, pow_one, Complex.mul_re, c_re, c_re, c_im, c_im]; ring
--   -- Im(cos θ^2) = 0
--   have c2_im: (Complex.cos θ ^ 2 ).im = 0  := by
--     nth_rw 1 [(by norm_num : 2 = 1 + 1), pow_add, pow_one, pow_one, Complex.mul_im, c_re, c_re, c_im, c_im]; ring
--   -- Re(cos θ^3) = cos θ^3
--   have c3_re: (Complex.cos θ ^ 3 ).re = Real.cos θ ^ 3  := by
--     nth_rw 1 [(by norm_num : 3 = 1 + 2), pow_add, pow_one, Complex.mul_re, c_re, c2_re, c_im, c2_im];ring
--   -- Im(cos θ^3) = 0
--   have c3_im: (Complex.cos θ ^ 3 ).im = 0  := by
--     nth_rw 1 [(by norm_num : 3 = 1 + 2), pow_add, pow_one, Complex.mul_im, c_re, c2_re, c_im, c2_im];ring
--   -- Re(sin θ) = sin θ
--   have s_re: (Complex.sin θ ).re = Real.sin θ  := by rfl
--   -- Im(sin θ) = 0
--   have s_im: (Complex.sin θ ).im = 0  := by exact Complex.sin_ofReal_im θ
--   -- Re(sin θ^2) = sin θ^2
--   have s2_re: (Complex.sin θ ^ 2 ).re = Real.sin θ ^ 2  := by
--     nth_rw 1 [(by norm_num : 2 = 1 + 1), pow_add, pow_one, pow_one, Complex.mul_re, s_re, s_re, s_im, s_im]; ring
--   -- Im(sin θ^2) = 0
--   have s2_im: (Complex.sin θ ^ 2 ).im = 0  := by
--     nth_rw 1 [(by norm_num : 2 = 1 + 1), pow_add, pow_one, pow_one, Complex.mul_im, s_re, s_re, s_im, s_im]; ring
--   -- Re(sin θ^3) = sin θ^3
--   have s3_re: (Complex.sin θ ^ 3 ).re = Real.sin θ ^ 3  := by
--     nth_rw 1 [(by norm_num : 3 = 1 + 2), pow_add, pow_one, Complex.mul_re, s_re, s2_re, s_im, s2_im];ring
--   -- Im(sin θ^3) = 0
--   have s3_im: (Complex.sin θ ^ 3 ).im = 0  := by
--     nth_rw 1 [(by norm_num : 3 = 1 + 2), pow_add, pow_one, Complex.mul_im, s_re, s2_re, s_im, s2_im];ring
--   --Prove that $Re(e^{i θ}^3)= Re(4 cos^3 θ - 3 cos θ + i (3 sin θ  - 4 sin^3 θ ))=4 cos^3 θ - 3 cos θ$
--   have costhree': (Complex.exp (3 * θ * Complex.I)).re = 4 * (Real.cos θ) ^ 3 - 3 * Real.cos θ := by
--     rw [Complex.exp_mul_I  (3 * θ), ← thete_pow_three', thete_pow_three]
--     -- rw [add_comm, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.I_re, mul_zero,Complex.sub_im,Complex.mul_im,(by exact rfl : Complex.re 3 = 3),(by exact rfl : Complex.im 3 = 0),s_re,s_im,Complex.mul_im,(by exact rfl : Complex.re 4 = 4),(by exact rfl : Complex.im 4 = 0),s3_re,s3_im,mul_zero,zero_mul,mul_zero,zero_mul,Complex.I_im,mul_one,zero_sub,zero_add,sub_zero,neg_zero,zero_add,Complex.sub_re,Complex.mul_re,c3_re,c3_im,mul_zero,sub_zero,(by exact rfl : Complex.re 4 = 4),Complex.mul_re,c_re,c_im,mul_zero,sub_zero,(by exact rfl : Complex.re 3 = 3)]
--     simp [add_comm, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.I_re]
--   -- Then we know that $cos 3 θ=4 cos^3 θ - 3 cos θ$
--   rw [costhree] at costhree'
--   exact costhree'
