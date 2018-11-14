import analysis.real
import xenalib.real_nth_root

open real

/-
We use the "real" real numbers in this question.

The xenalib.real_nth_root gives us the following commands:

nth_root (x : ℝ) (n : ℕ) -- n'th root of x

nth_root_pos : ∀ {x : ℝ} {n : ℕ}, x > 0 → n > 0 → nth_root x n > 0

nth_root_unique : ∀ {x y : ℝ} {n : ℕ}, 0 < x → 0 < y → 0 < n → y ^ n = x → y = nth_root x n

-/

-- preliminary lemma

theorem nth_root_mono' {x : ℝ} {n : ℕ} (Hxpos : 0 < x)
  (Hnpos : 0 < n) (y : ℝ) : x < y → x ^ n < y ^ n := sorry

-- change the inequality if you think it goes the other way
theorem Sht3Q3a : nth_root 3 (3 * 10 ^ 12) < nth_root 2 (2 * 10 ^ 12) := sorry

-- change the inequality if you think it goes the other way
theorem Sht3Q3b : 100^10000 < 10000^100 := sorry 

-- replace with the right explicit real number
theorem Sht3Q03ci : nth_root (2 ^ 22) 2 = (0 : ℝ) := sorry

-- replace with the right explicit real number
theorem Sht3Q03cii : nth_root (2 ^ 2 ^ 22) 2 = (0 : ℝ) := sorry
