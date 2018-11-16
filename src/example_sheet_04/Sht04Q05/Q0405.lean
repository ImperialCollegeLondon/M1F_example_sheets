-- NOTE : I (KB) HAVE NOT TYPED UP SOLUTIONS TO THIS QUESTION
-- SO THERE MIGHT BE MISTAKES.

import data.complex.basic

theorem Q0405b (z : ℂ) (Hz : z ≠ 0) :
∃ w₁ w₂ w₃ : ℂ, w₁ ^ 3 = z ∧ w₂ ^ 3 = z ∧ w₃ ^ 3 = z
  ∧ w₁ ≠ w₂ ∧ w₂ ≠ w₃ ∧ w₃ ≠ w₁
  ∧ complex.abs (w₁ - w₂) = complex.abs (w₂ - w₃)
  ∧ complex.abs (w₂ - w₃) = complex.abs (w₃ - w₁) := sorry