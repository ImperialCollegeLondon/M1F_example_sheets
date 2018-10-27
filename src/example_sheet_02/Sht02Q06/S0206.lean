import data.real.basic
import tactic.norm_num

open real

theorem Q6 : sqrt 2 + sqrt 6 < sqrt 15 :=
begin
  apply lt_of_not_ge,
  intro H,
  have H2 := mul_self_le_mul_self (sqrt_prop 15).1 H,
  rw [(sqrt_prop 15).2,add_mul_self_eq,(sqrt_prop 2).2,(sqrt_prop 6).2] at H2,
  have H3 : 15 ≤ 2 + (6 + 2 * sqrt 2 * sqrt 6),
    revert H2,norm_num,
  rw [←sub_le_iff_le_add',←sub_le_iff_le_add',mul_assoc,
      ←div_le_iff' (show (0 : ℝ) < 2, by norm_num)] at H3,
  have H4 := mul_self_le_mul_self (by norm_num) H3,
  rw mul_assoc at H4,
  rw mul_comm (sqrt 6) at H4,
  rw mul_assoc at H4,
  rw (sqrt_prop 6).2 at H4,
  rw ←mul_assoc at H4,
  rw (sqrt_prop 2).2 at H4,
  revert H4,
  norm_num
end
