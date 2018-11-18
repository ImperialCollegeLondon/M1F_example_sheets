-- induction on naturals starting with base case m

theorem modified_induction {P : nat → Prop} {m} (h0 : P m) (h1 : ∀ n ≥ m, P n → P (n + 1)) : ∀ n ≥ m, P n :=
begin
  intro n,
  apply nat.strong_induction_on n, intros n IH h,
  cases lt_or_eq_of_le h with lt eq,
  { cases n with n, {cases lt},
    have := nat.le_of_lt_succ lt,
    exact h1 _ this (IH _ (nat.lt_succ_self _) this) },
  { subst n, exact h0 }
end
