import data.real.basic

theorem Q5a_true : ∀ (x : ℝ), ∃ (y : ℝ), x + y = 2 := sorry
theorem Q5a_false : ¬ (∀ (x : ℝ), ∃ (y : ℝ), x + y = 2) := sorry

theorem Q5b_true : ∃ (y : ℝ), ∀ (x : ℝ), x + y = 2 := sorry
theorem Q5b_false : ¬ (∃ (y : ℝ), ∀ (x : ℝ), x + y = 2) := sorry
