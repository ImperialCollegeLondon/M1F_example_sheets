-- IMPORTANT NOTE: I (KB) HAVE NOT TYPED UP A SOLUTION TO THIS SO THERE MIGHT BE ERRORS

import data.real.basic
import analysis.exponential

theorem Q0201b (x : ℝ) : let y := x - 2 in 
3 * x ^ 3 - 18 * x ^ 2 + 27 * x - 4 = 3 * y ^ 3 - 9 * y + 2 := sorry

theorem Q0201c (y : ℝ) : let c := y / 2 in
3 * y ^ 3 - 9 * y + 2 = 0 ↔ 4 * c ^ 3 - 3 * c + 1 / 3 = 0 := sorry

open real

theorem Q0201d (c : ℝ) : let θ := arccos c in
4 * c ^ 3 - 3 * c + 1 / 3 = 0 ↔ cos (3 * θ) = - 1 / 3 := sorry

theorem Q0201e : let θ := arccos (- 1 / 3) / 3 in let c := cos θ in let y := 2 * c in let x := y + 2 in 
3 * x ^ 3 - 18 * x ^ 2 + 27 * x = 0 := sorry

-- find explicit values for x₂ and x₃ 
theorem Q0201f : 
let θ := arccos (- 1 / 3) / 3 in let c := cos θ in let y := 2 * c in let x₁ := y + 2 in 
let x₂ := (0 : ℝ) in 
let x₃ := (0 : ℝ) in 
let L := [x₁, x₂, x₃] in
list.nodup L ∧
∀ x : ℝ, x ∈ L → 3 * x ^ 3 - 18 * x ^ 2 + 27 * x = 0 := sorry
