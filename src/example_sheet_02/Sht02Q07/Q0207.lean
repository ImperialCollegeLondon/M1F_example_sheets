/- Q7 : are the following numbers rational or irrational
(a) sqrt(2)+sqrt(3/2)
(b) 1+sqrt(2)+sqrt(3/2)
(c) 2sqrt(18)-3sqrt(8)
-/

import data.real.irrational

open real

-- delete as appropriate

theorem Q0207a_irrat : irrational (sqrt 2 + sqrt (3 / 2)) := sorry 
theorem Q0207a_rat : ∃ (q : ℚ), sqrt 2 + sqrt (3 / 2) = q := sorry 

theorem Q0207b_irrat : irrational (1 + sqrt 2 + sqrt (3 / 2)) := sorry
theorem Q0207b_rat : ∃ (q : ℚ), 1 + sqrt 2 + sqrt (3 / 2) = q := sorry

theorem Q0207c_irrat : irrational (2 * sqrt 18 - 3 * sqrt 8) := sorry
theorem Q0207c_rat : ∃ (q : ℚ), 2 * sqrt 18 - 3 * sqrt 8 = q := sorry
