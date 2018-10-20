import data.real.basic

def open_zero_one := {x : ℝ | 0 < x ∧ x < 1}

-- open_zero_one has no maximal element
theorem Q2 : ¬ (∃ m : ℝ, m ∈ open_zero_one ∧ 
                  ∀ x : ℝ, x ∈ open_zero_one → x ≤ m) := sorry
        