--import xenalib.M1Fstuff algebra.group_power xenalib.square_root xenalib.complex
import analysis.real


theorem Q5a (t x:ℝ) (H:t>0) : abs x < t ↔ -t < x ∧ x < t := 
begin
exact abs_lt,
end

theorem Q5c (x:ℝ) : abs (x-2) < abs (x-4) ↔ x < 3 :=
begin
split,
  intro H,
  cases lt_or_ge x 4 with H2 H2,
    rw [abs_of_neg (sub_neg_of_lt H2)] at H,
    have H3 : x-2 < -(x-4) := calc x-2 ≤ abs (x-2) : le_abs_self (x-2) ... < -(x-4) : H,
    rw [neg_sub] at H3,
    have H4 := sub_neg_of_lt H3,
    rw [sub_sub,add_sub] at H4,
    have H5 : (2:ℝ)+4=6 := by norm_num,
    rw [H5,←sub_add,sub_add_eq_add_sub,←two_mul,lt_iff_sub_neg] at H4,
    have H6 : 2⁻¹ * (2*x) < 2⁻¹ * 6 := mul_lt_mul_of_pos_left H4 (by norm_num),
    norm_num at H6,
    exact H6,
  exfalso,
  have H3 : x-2 < x-2 := calc
  x-2 ≤ abs(x-2) : le_abs_self (x-2)
  ... < abs(x-4) : H
  ... = x-4 : abs_of_nonneg (_) 
  ... < x-2 : (sub_lt_sub_iff_left x).2 _,
      exact lt_irrefl (x-2) H3,
    exact sub_nonneg_of_le H2,
  { norm_num },
intro Hx_lt_3,
suffices : abs (x-2) < 4-x,
  apply lt_of_lt_of_le this,
  rw [←neg_sub x 4],
  exact neg_le_abs_self (x-4),
apply (abs_lt).2,
split,
  rw [neg_sub],
  exact (sub_lt_sub_iff_left x).2 (by norm_num),
  apply @lt_trans _ _ (x-2) 1 (4-x),
  exact calc _ < 3-2 : (sub_lt_sub_iff_right (2:ℝ)).2 Hx_lt_3
  ... =1 : by norm_num,
apply lt_of_sub_pos,
have := sub_pos_of_lt Hx_lt_3,
have H : (4:ℝ)=3+1 := by norm_num,
rw [H],
suffices H2 : 3+1-x-1 = 3-x,
  rw [H2],
  assumption,
simp,
end

-- probably these should be done with "fake complexes", defined
-- using addition and multiplication on R^2. But given that I
-- just actually wrote a proper implementation of the complexes
-- in Lean, I am just going to use them, but still give the
-- proofs which I was looking for rather than just noting that
-- Lean knows complexes are associative etc.

theorem Q6a : ∀ p q r : complex, (p+q)+r=p+(q+r) :=
begin
intros,
apply complex.eq_of_re_eq_and_im_eq,
split,
  repeat {rw [complex.proj_add_re]},
  exact @add_assoc ℝ _ _ _ _,
repeat {rw [complex.proj_add_im]},
exact @add_assoc ℝ _ _ _ _,
end 

theorem Q6b : ∀ p q : complex, p*q=q*p :=
begin
intros,
apply complex.eq_of_re_eq_and_im_eq,
repeat {rw [complex.proj_mul_re,complex.proj_mul_im]},
split;simp,
end 

theorem Q6c : ∀ p q : complex, complex.conjugate p * complex.conjugate q = complex.conjugate (p*q) :=
begin
intros,
unfold complex.conjugate,
apply complex.eq_of_re_eq_and_im_eq,
repeat {rw [complex.proj_mul_re,complex.proj_mul_im]},
simp,
end

theorem Q7 (z : complex) (H : z^2=-1) : z=complex.I ∨ z = -complex.I :=
begin
rw [pow_two_eq_mul_self] at H,
have Him : (z*z).im = 0,
  rw [H],
  rw [complex.proj_neg_im,complex.proj_one_im,neg_zero],
have Hre : (z*z).re = -1,
  rw [H],
  rw [complex.proj_neg_re,complex.proj_one_re],
rw [complex.proj_mul_im,mul_comm,←two_mul,mul_eq_zero] at Him,
cases Him with Hfalse Him,
  revert Hfalse,norm_num,
rw [mul_eq_zero] at Him,
rw [complex.proj_mul_re] at Hre,
cases Him with Hfalse Htrue,
  rw [Hfalse,mul_zero,sub_zero] at Hre,
  have : -(1:ℝ)≥0 := calc -1 = z.re*z.re : eq.symm Hre ... ≥ 0 : mul_self_nonneg _,
  norm_num at this,
rw [Htrue] at Hre,
have H1 : z.im*z.im=1, simpa using Hre,
have H2 : z.im = 1 ∨ z.im = -1 := (mul_self_eq_one_iff z.im).1 H1,
cases H2 with Hi Hmi,
  left,rw [complex.eq_iff_re_eq_and_im_eq,Htrue,Hi],split;refl, 
  right,rw [complex.eq_iff_re_eq_and_im_eq,Htrue,Hmi],split;
    simp [complex.proj_neg_re,complex.proj_neg_im,complex.proj_I_re,complex.proj_I_im], 
end

end M1F_Sheet03
