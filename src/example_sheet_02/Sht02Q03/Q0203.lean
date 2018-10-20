import data.rat
import data.real.basic

theorem Q3a (n : int) : (3 : ℤ) ∣ n ^ 2 → (3 : ℤ) ∣ n := sorry

-- Two ways to formalise second part. First way does not use existence
-- of sqrt(3) (or indeed of the real numbers at all)

theorem no_rational_squared_is_three : ¬ (∃ (q : ℚ), q ^ 2 = 3) := sorry

-- second way says that the real number sqrt(3) is not in the image of the map
-- from the rationals to the reals

theorem no_rational_is_sqrt_three : ¬ (∃ (q : ℚ), (q : ℝ) = real.sqrt 3) := sorry
