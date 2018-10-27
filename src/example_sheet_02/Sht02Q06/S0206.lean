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
  rw sub_le
end

#check add_mul_self