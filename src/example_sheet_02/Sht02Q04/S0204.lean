import xenalib.irrational

open real

theorem Q4a_false : ¬ (∀ (x y : ℝ), irrational x → irrational y → irrational (x+y)) :=
begin
  intro H,
  have H2 := H (sqrt 2) (-sqrt 2),
  have H3 := H2 sqrt_two_irrational (neg_irrat sqrt_two_irrational),
  apply H3,
  existsi (0 : ℚ),
  simp
end

theorem Q4b_false : ¬ (∀ (a : ℝ), ∀ (b : ℚ), irrational a → irrational (a*b)) :=
begin
  intro H,
  apply H (sqrt 2) 0 sqrt_two_irrational,
  existsi (0 : ℚ),
  simp
end
