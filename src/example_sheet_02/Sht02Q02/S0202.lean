import data.real.basic
import tactic.linarith

def open_zero_one := {x : ℝ | 0 < x ∧ x < 1}

-- open_zero_one has no maximal element
theorem Q2 : ¬ (∃ m : ℝ, m ∈ open_zero_one ∧ 
                  ∀ x : ℝ, x ∈ open_zero_one → x ≤ m) :=
begin
  rintro ⟨m,⟨H1,H2⟩,Hx⟩,
  -- now apply max hypothesis to (m + 1) / 2.
  have H := Hx ((m + 1) / 2),
  -- Can only use the hypothesis if we know (m + 1) / 2 is in the interval.
  have Hav : (m + 1) / 2 ∈ open_zero_one,
    split,
      -- now 0 < m is a hypothesis and 0 < (m + 1) / 2 is the goal
      linarith, -- and this tactic does it
    -- similarly hypothesis m < 1 implies goal (m + 1) / 2 < 1
    linarith,
  -- now use that m is supposed to be the max.
  have Hwrong := H Hav, 
  -- hypothesis Hwrong (m + 1) / 2 <= m contradicts hypothesis m < 1.
  -- Contradictory hypos means we can even prove a false goal.
  linarith,
end
