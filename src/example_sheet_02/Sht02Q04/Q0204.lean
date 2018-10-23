import data.real.basic
import data.real.irrational

/-
Students need to know that the import gives them
sqrt_two_irrational : irrational (sqrt 2)
-/

theorem Q4a_true : ∀ (x y : ℝ), irrational x → irrational y → irrational (x+y) := sorry
theorem Q4a_false : ¬ (∀ (x y : ℝ), irrational x → irrational y → irrational (x+y)) := sorry

theorem Q4b_true : ∀ (a : ℝ), ∀ (b : ℚ), irrational a → irrational (a*b) := sorry
theorem Q4b_false : ¬ (∀ (a : ℝ), ∀ (b : ℚ), irrational a → irrational (a*b)) := sorry
