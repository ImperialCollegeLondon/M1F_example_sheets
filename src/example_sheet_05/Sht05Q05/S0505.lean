import tactic.ring

lemma lemma1 {a b n : ℕ} (H : 6 * a + 9 * b = n) : 3 ∣ n :=
begin
  existsi (2 * a + 3 * b),
  rw ←H,
  ring  
end

theorem Q0505 :
  ¬ (∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = 43)
  ∧ ∀ m, m > 43 → ∃ a b c : ℕ, 6 * a + 9 * b + 20 * c = m :=
begin
  split,
  { -- first show 43 can't be done.
    rintro ⟨a,b,c,H⟩,
    cases c with c,
      -- case c = 0
      rw [mul_zero,add_zero] at H,
      have H2 : 3 ∣ 43 := lemma1 H,
      revert H2, exact dec_trivial,
    cases c with c,
      -- case c = 1
      replace H := add_right_cancel H,
      have H2 : 3 ∣ 23 := lemma1 H,
      revert H2, exact dec_trivial,
    cases c with e,
      -- case c = 2
      replace H := add_right_cancel H,
      cases a with a,
        cases b with b,
          revert H,exact dec_trivial,
        cases H,
      change _ * (a + 1) + _ = _ at H,
      rw [mul_add,mul_one] at H,
      have : 6 ≤ 3 := calc
        6   ≤ (6 * a) + 6 : nat.le_add_left _ _
        ... ≤ (6 * a) + 6 + 9 * b : nat.le_add_right _ _
        ... = 3 : by rw H,
      revert this,
      exact dec_trivial,
    -- case c >= 3
    change _ + 20 * (e + 3) = _ at H,
    rw mul_add at H,
    have : 20 * 3 ≤ 43 := calc
      20 * 3 ≤ 20 * e + 20 * 3 : nat.le_add_left _ _
      ...    ≤ _ + (20 * e + 20 * 3) : nat.le_add_left _ _
      ...    = 43 : by rw H,
    revert this, exact dec_trivial
  },

  -- now the proof that it's true for 44 or more by induction

  -- first formalise the hypothesis we're going to prove.
    
  let P : ℕ → Prop := λ n, ∀ r : ℕ, r < 6 → (∃ (a b c : ℕ), 6 * a + 9 * b + 20 * c = 44 + (r + 6 * n)),
  
  -- reduce to checking P n for all n

  suffices : ∀ n, P n,
  { intros m Hm,
    rw (show m = 44 + (m - 44), from eq.symm (nat.add_sub_cancel' Hm)),
    rw ←(nat.mod_add_div (m - 44) 6),
    refine this ((m - 44) / 6) ((m - 44) % 6) _,
    exact nat.mod_lt _ dec_trivial
  },

  -- now prove P n for all n by induction

  intro n, induction n with d Hd,
    -- base case, `exacts` trick due to Kenny
    { intros r Hr,
      repeat { cases Hr with _ Hr },
      exacts [⟨0, 1, 2, rfl⟩,
              ⟨8, 0, 0, rfl⟩,
              ⟨0, 3, 1, rfl⟩,
              ⟨1, 0, 2, rfl⟩,
              ⟨0, 5, 0, rfl⟩,
              ⟨4, 0, 1, rfl⟩]
    },
  -- inductive step
  intros r Hr,
  rcases Hd r Hr with ⟨a, b, c, H⟩,
  existsi a + 1,
  existsi b,
  existsi c,
  rw (show 6 * (a + 1) + 9 * b + 20 * c = (6 * a + 9 * b + 20 * c) + 6, by ring),
  rw H,
  rw nat.succ_eq_add_one,
  ring,
  end
