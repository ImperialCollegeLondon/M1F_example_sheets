import analysis.real
variables x t : ℝ

noncomputable def abv (x : ℝ) := if x ≥ 0 then x else -x

theorem Q0305a (Ht : t > 0) : abv x < t ↔ -t < x ∧ x < t := sorry

-- change the RHS to the correct explicit range
theorem Q0305b : abv (x + 1) < 3 ↔ x = 37 := sorry

-- change the RHS to the correct explicit range
theorem Q0305c : abv (x - 2) < abv (x - 4) ↔ x = 37 := sorry
