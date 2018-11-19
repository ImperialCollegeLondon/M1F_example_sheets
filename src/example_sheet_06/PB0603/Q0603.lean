import data.real.basic

definition is_bounded_above (S : set ℝ) := ∃ b : ℝ, ∀ s ∈ S, s ≤ b

-- chose which one to prove, comment out the other.

theorem Q0603_yes : ∃ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) ∧ is_bounded_above S := sorry 
theorem Q0603_no : ∀ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) → ¬ is_bounded_above S := sorry
