import data.real.irrational
import analysis.exponential

open real

lemma irrat_add_rat {x : ℝ} {y : ℚ} : irrational x → irrational (x + y) := sorry

lemma rat_add_irrat {x : ℚ} {y : ℝ} : irrational y → irrational (x + y) := sorry

lemma irrat_mul_rat {x : ℝ} {y : ℚ} : y ≠ 0 → irrational x → irrational (x * y) := sorry

lemma rat_mul_irrat {x : ℚ} {y : ℝ} : x ≠ 0 → irrational y → irrational (x * y) := sorry

lemma neg_irrat {x : ℝ} : irrational x → irrational (-x) := sorry

lemma e_irrat : irrational (exp 1) := sorry