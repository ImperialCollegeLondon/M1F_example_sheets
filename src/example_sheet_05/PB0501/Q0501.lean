--import algebra.group_power tactic.norm_num algebra.big_operators

def Fib : ℕ → ℕ
| 0 := 37 -- question only defines F_n for n>=1 so set F_0 = junk value
| 1 := 1
| 2 := 1
| (n + 3) := Fib (n + 1) + Fib (n + 2)

def is_even (n : ℕ) : Prop := ∃ k, n = 2 * k
def is_odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

-- starting at 0 would have been such a better idea
theorem Q1a : ∀ n : ℕ, n ≥ 1 →
  is_odd (Fib (3 * n - 2)) ∧ is_odd (Fib (3 * n - 1)) ∧ is_even (Fib (3 * n)) := sorry

theorem Q1b : is_even (Fib (2018)) := sorry

