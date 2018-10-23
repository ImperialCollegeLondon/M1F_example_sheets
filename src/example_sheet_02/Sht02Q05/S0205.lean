import data.real.basic
import tactic.norm_num
import tactic.ring

theorem Q5a_true : ∀ (x : ℝ), ∃ (y : ℝ), x + y = 2 :=
begin
  intro x,
  existsi (2 - x),
  simp, -- norm_num also works, as does ring
end

theorem Q5b_false : ¬ (∃ (y : ℝ), ∀ (x : ℝ), x + y = 2) :=
begin
  intro H,
  cases H with y Hy,
  have H := Hy (3 - y),
  norm_num at H,
end
