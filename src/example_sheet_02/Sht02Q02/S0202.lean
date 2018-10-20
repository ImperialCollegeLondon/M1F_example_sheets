import data.real.basic
import tactic.linarith

def open_zero_one := {x : ℝ | 0 < x ∧ x < 1}

-- open_zero_one has no maximal element
theorem Q2 : ¬ (∃ m : ℝ, m ∈ open_zero_one ∧ 
                  ∀ x : ℝ, x ∈ open_zero_one → x ≤ m) :=
begin
  rintro ⟨m,⟨H1,H2⟩,Hx⟩,
  have H := Hx ((m + 1) / 2),
  have Hav : (m + 1) / 2 ∈ open_zero_one,
    split,
      linarith,
    linarith,
  have Hwrong := H Hav,
  linarith,
end
