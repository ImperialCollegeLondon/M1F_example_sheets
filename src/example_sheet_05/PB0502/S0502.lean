import algebra.group_power

theorem Q0502 (n : ℕ) : n ≥ 2 → 4 ^ n > 3 ^ n + 2 ^ n :=
begin
  intro Hn2,
  -- hypotheses    n : ℕ
  --             Hn2 : n ≥ 2
  -- now replace n with m + 2 and then do induction on m >= 0
  cases n with n, cases Hn2, -- Hn2 : 0 ≥ 2 and cases kills it.
  cases n with m, revert Hn2, exact dec_trivial, -- here Hn2 : 1 ≥ 2 and cases doesn't kill it
  clear Hn2, -- and we're finally ready to go
  induction m with e He,
  -- it would have been nice just to be able to write modified_induction n Hn2 with d Hd...
    exact dec_trivial, -- base case
  generalize Hd : nat.succ (nat.succ e) = d,
  rw Hd at He,
  clear Hd e,
  /- context is *finally*
  e : ℕ,
  Hd : 4 ^ e > 3 ^ e + 2 ^ e
  ⊢ 4 ^ nat.succ e > 3 ^ nat.succ e + 2 ^ nat.succ e
  -/
  exact calc
    4 ^ nat.succ d > (3 ^ d + 2 ^ d) * 4 : mul_lt_mul_of_pos_right Hd dec_trivial
    ...            = 3 ^ d * 4 + 2 ^ d * 4 : by rw add_mul
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _,
end
