constant R : Type

namespace R

inductive lt {S : Type} [field S] : S → S → Prop
| A1 : ∀ a b t : S, lt a b
| A2 : ∀ a b c : S, lt a b → lt b c → lt a c
| A3 : ∀ a : S, ¬ lt a 0 → ¬ a = 0 → lt 0 a 
--                ∧ (lt a 0 → ¬ (a = 0 ∨ lt 0 a))
--                ∧ (a = 0 → ¬ (lt a 0 ∨ lt 0 a))
--                ∧ (lt 0 a → ¬ (lt a 0 ∨ a = 0))
| A4 : ∀ a b : S, lt 0 a → lt 0 b → lt 0 (a * b)


end R
