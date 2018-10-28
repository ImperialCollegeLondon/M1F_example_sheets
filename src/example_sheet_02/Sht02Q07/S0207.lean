import data.real.irrational
import xenalib.irrational
import tactic.norm_num
import example_sheet_02.Sht02Q03.S0203

open real

theorem Q0207a_irrat : irrational (sqrt 2 + sqrt (3 / 2)) := 
begin
  rintro ⟨q,Hq⟩,
  have H2 : (sqrt 2 + sqrt (3 / 2)) * (sqrt 2 + sqrt (3 / 2)) = q * q,
    rw Hq,
  rw add_mul_self_eq at H2,
  rw (sqrt_prop 2).2 at H2,
  rw (sqrt_prop ((3 : ℝ) / 2)).2 at H2,
  rw [mul_assoc,←sqrt_mul] at H2,
  rw (show max (0 : ℝ) 2 = 2, by norm_num) at H2,
  rw (show max (0 : ℝ) (3 / 2) = 3 / 2, by norm_num) at H2,
  rw (show (2 : ℝ) * (3 / 2) = 3, by norm_num) at H2,swap,norm_num,
  have H3 : sqrt 3 = (q * q - 2 - 3 / 2) / 2,
  rw ←H2,ring,
  have H4 : (((q * q - 2 - 3 / 2) / 2) : ℝ) = (((q * q - 2 - 3 / 2) / 2) : ℚ),
    simp,
  have H5 : (sqrt 3) ^ 2 = 3,
    rw [pow_two,(sqrt_prop 3).2],
    norm_num, 
  rw H3 at H5,
  rw H4 at H5,
  rw (show (3 : ℝ) = (3 : ℚ), by norm_num) at H5,
  apply no_rational_squared_is_three, -- from sheet 2 question 3
  existsi (q * q - 2 - 3 / 2) / 2,
  rw ←@rat.cast_inj ℝ _ _,
  rw ←H5,
  rw pow_two,
  rw pow_two,
  simp,  
end


theorem Q0207b_irrat : irrational (1 + sqrt 2 + sqrt (3 / 2)) := 
begin
  rintro ⟨q,Hq⟩,
  apply Q0207a_irrat,
  existsi (q-1),
  rw rat.cast_sub,
  rw ←Hq,
  simp,
end

theorem Q0207c_rat : ∃ (q : ℚ), 2 * sqrt 18 - 3 * sqrt 8 = q := ⟨0,begin 
  rw [(show ((0 : ℚ) : ℝ) = 0, by simp),sub_eq_zero],
  rw (show (18 : ℝ) = 2 * 3 ^ 2, by norm_num),
  rw (show (8 : ℝ) = 2 * 2 ^ 2, by norm_num),
  rw sqrt_mul _ (3 ^ 2),swap,norm_num,
  rw sqrt_mul _ (2 ^ 2),swap,norm_num,
  rw sqrt_sqr,swap,norm_num,
  rw sqrt_sqr,swap,norm_num,
  rw [mul_comm,←mul_assoc,mul_comm (sqrt 2)],
end⟩
