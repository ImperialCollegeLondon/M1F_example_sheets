/-
M1F 2018-19 Sheet 1 Question 1
Author : Kevin Buzzard

Tested with lean 3.4.1 and mathlib from September 2018.
-/

import data.real.basic -- real numbers

import xenalib.quadroots

--quadroots {x : ℝ} : x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 ∨ x = 2

-- you can rewrite this if you need it.

-- part (a) -- delete one of these and prove the other.

theorem M1F_sheet01_Q01a_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1 := sorry
theorem M1F_sheet01_Q01a_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → x = 1) := sorry

-- part (b) etc etc.

theorem M1F_sheet01_Q01b_is_T : ∀ x : ℝ, x = 1 → x ^ 2 - 3 * x + 2 = 0 := sorry
theorem M1F_sheet01_Q01b_is_F : ¬ (∀ x : ℝ, x = 1 → x ^ 2 - 3 * x + 2 = 0) := sorry

-- part (c)

theorem M1F_sheet01_Q01c_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ x = 1 := sorry
theorem M1F_sheet01_Q01c_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ x = 1) := sorry

-- part (d)

theorem M1F_sheet01_Q01d_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x = 2) := sorry
theorem M1F_sheet01_Q01d_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ↔ (x = 1 ∨ x =2)) := sorry

-- part (e)

theorem M1F_sheet01_Q01e_is_T : ∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → (x = 1 ∨ x = 2 ∨ x = 3) := sorry
theorem M1F_sheet01_Q01e_is_F : ¬ (∀ x : ℝ, x ^ 2 - 3 * x + 2 = 0 → (x = 1 ∨ x = 2 ∨ x = 3)) := sorry

-- part (f)

theorem M1F_sheet01_Q01f_is_T : ∀ x : ℝ, (x = 1 ∨ x = 2 ∨ x = 3) → x ^ 2 - 3 * x + 2 = 0  := sorry
theorem M1F_sheet01_Q01f_is_F : ¬ (∀ x : ℝ, (x = 1 ∨ x = 2 ∨ x = 3) → x ^ 2 - 3 * x + 2 = 0)  := sorry
