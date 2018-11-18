-- Both the formulation of the question and the
-- solution in Lean are due to Chris Hughes

import data.nat.basic

open nat

/-- Statement of "what the islanders know". Given a day number `d`, and the actual number of blue eyed
islanders `b`, and a hypothesized number of blue eyed islanders `B`, it returns whether or not `B` is a possible
number of blue eyed islanders from the blue eyed islanders' perspective. -/
def island_rules : ℕ → ℕ → ℕ → Prop
/- on day 0 there are two possibilities for the number of blue eyed islanders `b` and `b - 1`
  unless `b = 1`, in which case there is only one possibility, since it is also known that the actual number is greater than zero -/
| 0     b B := (B = b ∨ B = b - 1) ∧ 0 < B
/- On subsequent days, a hypothesized value `B` is possible if and only if it was possible the previous day and
  it is consistent with whether or not islanders left the previous day -/
| (d+1) b B := island_rules d b B ∧
  ((∀ C, island_rules d b C → C = b) ↔ ∀ C, island_rules d B C → C = B)

-- with this formulation one can prove that all the blue-eyed islanders leave on day 100
lemma blue_eyed_islander_100 {d : ℕ} : (∀ B, island_rules d 100 B → B = 100) ↔ 100 ≤ d + 1 := sorry