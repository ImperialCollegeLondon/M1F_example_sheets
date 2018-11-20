import data.real.basic

example (S : set ℝ) (x : ℝ) (Hx1 : x ∈ upper_bounds S) (Hx2 : x ∈ S) : is_lub S x :=
begin
  split,
    assumption,
  unfold lower_bounds,
  dsimp,
  intro a,
  intro Ha,
  apply Ha,
  assumption,
end