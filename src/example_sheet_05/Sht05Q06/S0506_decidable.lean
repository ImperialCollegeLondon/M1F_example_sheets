-- formalisation of question and solution due to Chris Hughes
-- This alternative solution gets Lean to simply compute everything up to 100
-- rather than using general reasoning. So it's shorter, but takes longer to compile.

import data.nat.prime data.finset
open nat

def island_rules : ℕ → ℕ → (ℕ → Prop)
| 0       b B := (B = b ∨ B = b - 1) ∧ B > 0
| (d + 1) b B := island_rules d b B ∧
 ((∀ C, island_rules d b C → C = b) ↔ ∀ C, island_rules d B C → C = B)

def island_rules2 : ℕ → ℕ → finset ℕ
| 0     b := ({b - 1, b} : finset ℕ).filter (> 0)
| (d+1) b := (island_rules2 d b).filter
  (λ B, (∀ C ∈ island_rules2 d b, C = b) ↔ (∀ C ∈ island_rules2 d B, C = B))

lemma island_rules_iff (d : ℕ) : ∀ b B, island_rules d b B ↔ B ∈ island_rules2 d b :=
by induction d; simp [island_rules, island_rules2, *]; finish

instance (d b B) : decidable (island_rules d b B) :=
decidable_of_iff _ (island_rules_iff _ _ _).symm

lemma island_rules_iff' (d : ℕ) : ∀ b, (∀ B, island_rules d b B → B = b) ↔ (∀ B ∈ island_rules2 d b, B = b) :=
by simp [island_rules_iff]

instance dec2 : decidable_rel (λ d b, ∀ B, island_rules d b B → B = b) :=
λ d b, decidable_of_iff _ (island_rules_iff' d b).symm

lemma blue_eyed_islander : ∀ d < 100, (∀ B, island_rules d 100 B → B = 100) ↔ d = 99 :=
dec_trivial