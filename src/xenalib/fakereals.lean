-- Mathlib's reals are called `real` so we'll go with `real'` for
-- the "fake" version

class real' (R : Type) :=
(is_field : field R)
(is_has_lt : has_lt R)
(A1 : ∀ {a b t : R}, a < b → a + t < b + t)
(A2 : ∀ {a b c : R}, a < b → b < c → a < c)
(A31 : ∀ a b : R, (a < b ∨ a = b ∨ b < a))
(A32 : ∀ a b : R, (a < b → ¬ a = b ∧ ¬ b < a) ∧ (a = b → ¬ b < a))
(A4 : ∀ {a b : R}, a > 0 → b > 0 → (a * b) > 0)

open real'

instance real'_is_field (R : Type) [real' R] : field R := is_field R
instance real'_has_lt (R : Type) [real' R] : has_lt R := is_has_lt R
instance rel'_zero_ne_one (R : Type) [real' R] : zero_ne_one_class R := by apply_instance

-- example of usage
theorem real'.one_pos (R : Type) [real' R] : (1 : R) > 0 :=
begin
  cases (A31 (0 : R) 1) with H1pos H1nonpos,
    assumption,
  cases H1nonpos with H1zero H1neg,
    exfalso,
    apply (zero_ne_one : (0 : R) = 1 → false),
    assumption,
  have H : (1 : R) + (-1) < 0 + (-1) := A1 H1neg,
    rw [add_neg_self,zero_add] at H,
  have H2 : (-1 : R) * (-1) > 0 := A4 H H,
  rw [←neg_eq_neg_one_mul,neg_neg] at H2,
  exact H2,
end