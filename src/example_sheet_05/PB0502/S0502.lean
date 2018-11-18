import algebra.group_power

-- This is more of a pain than it should be because we don't have induction starting at 2,
-- we only have induction starting at zero. Reid Barton says that `induction ... using ...`
-- should be usable though!

-- My second attempt is better than my first. I am hoping my third will be one I'm
-- happy with, when I get round to understanding how to use `using`.

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
    4 ^ nat.succ d > (3 ^ d + 2 ^ d) * 4 : mul_lt_mul_of_pos_right He dec_trivial
    ...            = 3 ^ d * 4 + 2 ^ d * 4 : by rw add_mul
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _,
end

theorem Q0502' (n : ℕ) : n ≥ 2 → 4 ^ n > 3 ^ n + 2 ^ n :=
begin
  induction n with d Hd,
    exact dec_trivial,
  -- now pick up the pieces for modified induction
  intro Hs, cases Hs,
    exact dec_trivial, -- base case n = 2,
  replace Hd := Hd Hs_a, clear Hs_a,
  /-
  d : ℕ,
  Hd : 4 ^ d > 3 ^ d + 2 ^ d
  ⊢ 4 ^ nat.succ d > 3 ^ nat.succ d + 2 ^ nat.succ d
  -/
    exact calc
    4 ^ nat.succ d > (3 ^ d + 2 ^ d) * 4 : mul_lt_mul_of_pos_right Hd dec_trivial
    ...            = 3 ^ d * 4 + 2 ^ d * 4 : by rw add_mul
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 4 : add_le_add_right (nat.mul_le_mul_left _ (dec_trivial)) _
    ...            ≥ 3 ^ d * 3 + 2 ^ d * 2 : add_le_add_left (nat.mul_le_mul_left _ (dec_trivial)) _,
end