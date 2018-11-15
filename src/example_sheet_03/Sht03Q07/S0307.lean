import example_sheet_03.Sht03Q06.S0306

namespace complex

definition I : ℂ := ⟨0,1⟩

@[simp] lemma I_re  : I.re = 0 := rfl
@[simp] lemma I_im  : I.im = 1 := rfl

protected definition neg : ℂ → ℂ := λ z, ⟨-z.re, -z.im⟩

instance : has_neg ℂ := ⟨complex.neg⟩

@[simp] lemma neg_re {z : ℂ} : (-z).re = -z.re := rfl
@[simp] lemma neg_im {z : ℂ} : (-z).im = -z.im := rfl

lemma mul_one {z : ℂ} : z * 1 = z := by check_on_real_and_imag_parts

protected def pow (z : ℂ) : ℕ → ℂ
| 0 := 1
| (n + 1) := z * pow n

instance : has_pow ℂ ℕ := ⟨complex.pow⟩

lemma pow_two_eq_mul_self {z : ℂ} : z ^ 2 = z * z :=
begin
  show z * (z * 1) = z * z,
  rw mul_one,
end

end complex

open complex

variable z : ℂ

theorem Q7 (H : z ^ 2 = -1) : z = I ∨ z = -I :=
begin
  rw ext_iff at H,
  cases H with H1 H2,
  rw pow_two_eq_mul_self at *,
  simp at *,
  rw [mul_comm,←mul_two] at H2,
  -- 2 * Re(z) * Im(z) = 0
  rw mul_eq_zero at H2,
  cases H2, swap, revert H2, norm_num,
  rw mul_eq_zero at H2,
  -- Re(z) = 0 or Im(z) = 0 
  cases H2,
  { -- Re(z) = 0
    rw H2 at H1,
    have H3 : z.im * z.im = 1,
      simpa using H1,
      rw mul_self_eq_one_iff at H3,
      cases H3,
        left, apply complex.ext, rw H2, rw H3,simp,
        right, apply complex.ext, rw H2, rw H3,simp,
  },
  { -- Im(z) = 0, a contradiction,
    rw H2 at H1,
    exfalso,
    have H3 : z.re * z.re = -1,
      simpa using H1,
    have H4 := mul_self_nonneg z.re,
    rw H3 at H4,
    revert H4,
    norm_num
  }
end