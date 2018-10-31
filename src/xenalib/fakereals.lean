-- Mathlib's reals are called `real` so we'll go with `real'` for
-- the "fake" version

-- for examples of usage of this class, see M1F_chapter2_lemmas.lean

class real' (R : Type) :=
(is_field : field R)
(is_has_lt : has_lt R)
(A1 : ∀ {a b t : R}, a < b → a + t < b + t)
(A2 : ∀ {a b c : R}, a < b → b < c → a < c)
(A31 : ∀ a b : R, (a < b ∨ a = b ∨ b < a))
(A32 : ∀ a b : R, (a < b → ¬ a = b ∧ ¬ b < a) ∧ (a = b → ¬ a < b))
(A4 : ∀ {a b : R}, a > 0 → b > 0 → (a * b) > 0)

open real' 

instance real'_is_field (R : Type) [real' R] : field R := is_field R
instance real'_has_lt (R : Type) [real' R] : has_lt R := is_has_lt R
instance rel'_zero_ne_one (R : Type) [real' R] : zero_ne_one_class R := by apply_instance

namespace real'

variables {R : Type} [real' R] {a b : R}

lemma ne_of_lt (H : a < b) : a ≠ b := ((A32 a b).1 H).1

lemma not_gt_of_lt (H : a < b) : ¬ (b < a) := ((A32 a b).1 H).2

lemma not_lt_of_eq (H : a = b) : ¬ (a < b) := ((A32 a b).2 H)

end real'