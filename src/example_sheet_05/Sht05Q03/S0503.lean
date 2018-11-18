import tactic.ring

-- inductive proof
theorem Q0503a (n : ℕ) : ∃ k, (n + 1) + (n + 2) + (n + 3) + (n + 4) = 4 * k + 2 :=
begin
  induction n with d Hd,
    -- base case
    existsi 2, refl,
  -- inductive step
  cases Hd with k Hk,
  existsi (k + 1),
  rw mul_add,
  change _ = (4 * k + 2) + 4,
  rw ←Hk,
  ring,
end

-- inductive proof
theorem Q0503b (n : ℕ) : 8 ∣ (11 : ℤ) ^ n  - (3 : ℤ) ^ n :=
begin
  induction n with d Hd,
    -- base case
    existsi (0 : ℤ), refl,
  -- inductive step
  cases Hd with k Hk,
  -- pencil and paper calculation gives...
  existsi (11 * k + 3 ^ d),
  change (11 : ℤ) * 11 ^ d - 3 * 3 ^ d = _,
  replace Hk : 11 ^ d = 8 * k + 3 ^ d := eq_add_of_sub_eq Hk,
  rw Hk,
  ring,
end

theorem Q0503c (n : ℕ) : ∃ k, (n + 1) + (n + 2) + (n + 3) + (n + 4) = 4 * k + 2 :=
begin
  existsi (n + 2),
  ring,
end

-- in Lean even the definition of the question for part (b) involves recursion.
