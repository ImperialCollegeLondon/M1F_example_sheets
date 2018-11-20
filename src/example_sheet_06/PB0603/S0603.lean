import data.real.basic
import data.set.basic
import tactic.norm_num
import tactic.linarith

example : set ℝ := ∅ 

definition is_bounded_above (S : set ℝ) := ∃ b : ℝ, ∀ s ∈ S, s ≤ b

-- the empty set works
theorem Q0603_yes : ∃ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) ∧ is_bounded_above S :=
begin
  existsi (∅ : set ℝ),
  split,
  { intro s,
    intro Hs,
    cases Hs,
  },
  { existsi (37 : ℝ),
    intro s,
    intro Hs,
    cases Hs
  }
end

-- but many non-empty sets work too
theorem Q0603_yes' : ∃ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) ∧ is_bounded_above S :=
begin
  let negreals := {x : ℝ | x < 0}, 
  existsi negreals,
  split,
  { intro s,
    intro Hs,
    change s < 0 at Hs,
    existsi (s / 2),
    split,
    { change s / 2 < 0,
      linarith,
    },
    linarith,
  },
  { existsi (37 : ℝ),
    intro s,
    intro Hs,
    change s < 0 at Hs,
    linarith,
  }
end
