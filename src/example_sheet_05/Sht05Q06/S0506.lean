-- Formalisation of question and solution by Chris Hughes

import data.nat.basic

open nat

/-- Statement of "what the islanders know". Given a day number `d`, and the actual number of blue eyed
islanders `b`, and a hypothesized number of blue eyed islanders `B`, it returns whether or not `B` is a possible
number of blue eyed islanders from the blue eyed islanders perspective. -/
def island_rules : ℕ → ℕ → ℕ → Prop
/- on day 0 there are two possibilities for the number of blue eyed islanders `b` and `b - 1`
  unless `b = 1`, in which case there is only one possibility, since it is also known that the actual number is greater than zero -/
| 0     b B := (B = b ∨ B = b - 1) ∧ 0 < B
/- On subsequent days, a hypothesized value `B` is possible if and only if it was possible the previous day and
  it is consistent with whether or not islanders left the previous day -/
| (d+1) b B := island_rules d b B ∧
  ((∀ C, island_rules d b C → C = b) ↔ ∀ C, island_rules d B C → C = B)

lemma island_rules_zero_of_island_rules : ∀ {d b B : ℕ}, island_rules d b B → (B = b ∨ B = b - 1) ∧ 0 < B
| 0     b B h := h
| (d+1) b B h := island_rules_zero_of_island_rules h.left

theorem blue_eyed_islander_mp : ∀ {d b}, 0 < b → b ≤ d + 1 → ∀ B, island_rules d b B → B = b
| 0 b hb0 hdb B hir := begin
    have : b = 1, from le_antisymm hdb (succ_le_of_lt hb0),
    unfold island_rules at hir,
    cases hir.left with h h,
    { exact h },
    { simp [this, *, lt_irrefl] at * }
  end
| (d+1) b hb hdbB B hir :=
  have (B = b ∨ B = b - 1) ∧ 0 < B, from island_rules_zero_of_island_rules hir,
  begin
    unfold island_rules at hir,
    cases this.left with h h,
    { exact h },
    { /- the case B = b - 1 -/
      have hb0 : 0 < b - 1, from h ▸ this.right,
      have hb1 : 1 ≤ b, from le_trans (succ_le_of_lt hb0) (nat.sub_le_self _ _),
      have hdbB' : b - 1 ≤ d + 1, from nat.sub_le_right_iff_le_add.2 hdbB,
      /- by our induction hypothesis, they would have left on day d if the actual number was b - 1 -/
      have ih : ∀ C : ℕ, island_rules d B C → C = B, from h.symm ▸ blue_eyed_islander_mp hb0 hdbB',
      /- From the definition of island_rules, this means they left yesterday -/
      rw ← hir.right at ih,
      /- Slightly strange proof, even though we know B = b - 1 and we're trying to prove
        B = b, we don't find a contradiction, we just prove B = b directly -/
      exact ih B hir.left }
  end

/-- This seems to come up over and over again, so I proved it seperately -/
theorem nat.sub_one_ne_self_of_pos {a : ℕ} (ha : 0 < a) : a - 1 ≠ a :=
ne_of_lt (nat.sub_lt_self ha dec_trivial)

/-- The other direction of the iff, stated in an easier to prove but equivalent way.
  If `d + 1` < b, then there are two possible values.  -/
lemma blue_eyed_islander_mpr : ∀ {d b}, 0 < b → d + 1 < b → ∀ B, island_rules d b B ↔ (B = b ∨ B = b - 1)
| 0     b hb0 hdb B := begin
  unfold island_rules,
  split,
  { exact λ h, h.left },
  { assume hbB,
    split,
    { exact hbB },
    { cases hbB with hbB hbB,
      { exact hbB.symm ▸ hb0 },
      { exact hbB.symm ▸ nat.sub_pos_of_lt hdb } } }
  end
| (succ d) b hb0 hdb B :=
begin
  split,
  { exact λ h, (island_rules_zero_of_island_rules h).left },
  { assume hbB,
    have hb10 : 0 < b - 1, from nat.sub_pos_of_lt (lt_trans dec_trivial hdb),
    have hdb1 : d + 1 < b - 1, from nat.lt_sub_right_of_add_lt hdb,
    /- Use our induction hypothesis twice. For both possible values of B, the islanders
      did not leave the previous day. This means we have no new information -/
    have ihb : ∀ B : ℕ, island_rules d b B ↔ B = b ∨ B = b - 1,
      from blue_eyed_islander_mpr hb0 (lt_trans (lt_succ_self _) hdb),
    have ihb1 : ∀ B : ℕ, island_rules d (b - 1) B ↔ B = b - 1 ∨ B = b - 1 - 1,
      from blue_eyed_islander_mpr hb10 hdb1,
    unfold island_rules,
    split,
    { rw ihb,
      exact hbB },
    /- the interesting part of the proof starts here, we have to prove that either value of B is
      possible -/
    { cases hbB with hbB hbB,
      { /- case B = b is easy -/
        rw hbB },
      { /- case B = b - 1 is harder -/
        /- By our induction hypotheses it was impossible to deduce the value of `b` yesterday in both
          the real world, and for our hypothesized value of `B`, which is `b - 1`. This means both sides
          of the iff statement are false -/
        simp only [ihb, ihb1, hbB],
        /- After applying the induction hypothesis, it is now obvious that both sides are false,
          and the proof is easy from now on -/
        apply iff_of_false,
        { assume h,
          have : b - 1 = b, from h (b - 1) (or.inr rfl),
          exact nat.sub_one_ne_self_of_pos hb0 this },
        { assume h,
          have : b - 1 - 1 = b - 1, from h (b - 1 - 1) (or.inr rfl),
          exact nat.sub_one_ne_self_of_pos hb10 this } } } }
end

lemma blue_eyed_islander {d b} (hb0 : 0 < b) : (∀ B, island_rules d b B → B = b) ↔ b ≤ d + 1 :=
begin
  split,
  { assume h,
    refine le_of_not_gt (λ hbd : d + 1 < b, _),
    have := blue_eyed_islander_mpr hb0 hbd,
    have : b - 1 = b, from h (b - 1) ((this (b - 1)).mpr (or.inr rfl)),
    exact nat.sub_one_ne_self_of_pos hb0 this },
  { exact blue_eyed_islander_mp hb0 }
end

lemma blue_eyed_islander_100 {d : ℕ} : (∀ B, island_rules d 100 B → B = 100) ↔ 100 ≤ d + 1 :=
blue_eyed_islander dec_trivial