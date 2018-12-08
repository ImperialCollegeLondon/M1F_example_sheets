import data.real.basic
import order.bounds
import tactic.linarith

-- theorem 6.3 of lectures: if l and m are both least upper bounds
-- for a set S of reals, then l = m
theorem sixpointthree 
  (S : set ℝ) (l m : ℝ) 
  (Hl : is_lub S l) (Hm : is_lub S m) : l = m :=
begin
  cases Hl with Hl1 Hl2,
  cases Hm with Hm1 Hm2,
  have Hlm : l ≤ m,
    apply Hl2,
    apply Hm1,
  have Hml : m ≤ l,
    apply Hm2,
    apply Hl1,
  linarith,
end

-- result from lectures : 59 is an upper bound for the empty set.
theorem empty_ub : (59 : ℝ) ∈ upper_bounds (∅ : set ℝ) :=
begin
  unfold upper_bounds,
  change ∀ (a : ℝ), a ∈ ∅ → a ≤ 59,
  intro a,
  intro H,
  cases H,
end

-- definition needed for example sheet 6 Q3
definition is_bounded_above (S : set ℝ) := ∃ b : ℝ, ∀ s ∈ S, s ≤ b

-- sheet 6 Q3 -- it is true that there can be a bounded-above set with the
-- property that ∀ s ∈ S, ∃ t ∈ S, s < t.

-- For example the empty set works:
theorem Q0603_yes : ∃ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) ∧ is_bounded_above S :=
begin
  existsi (∅ : set ℝ),
  split,
  { intro s,
    intro Hs,
    cases Hs,
  },
  { unfold is_bounded_above,
    existsi (59 : ℝ),
    intros s H, cases H,
  }
end

-- but this set works too
definition S01 := {x : ℝ | 0 < x ∧ x < 1}

theorem Q0603_yes' : ∃ S : set ℝ, (∀ s ∈ S, ∃ t ∈ S, s < t) ∧ is_bounded_above S :=
begin
  existsi S01,
  split,
  { intro s,
    intro Hs,
    existsi (s + 1) / 2,
    existsi _,
    { cases Hs,
      linarith},
    { cases Hs,
      split;linarith,
    }
  },
  { existsi (59 : ℝ),
    intro s,
    intro Hs,
    cases Hs,
    linarith,
  }
end

-- Example sheet 6 Q4 asks us to find the LUB of this set.
def Sa : set ℝ := {x : ℝ | x < 0}

-- this theorem proves it's zero.
theorem Q0604a_lub : is_lub Sa 0 :=
begin
  split,
  { intro a,
    intro Ha,
    change a < 0 at Ha,
    exact le_of_lt Ha},
  { intro b,
    intro Hb,
    unfold upper_bounds at Hb,
    dsimp at Hb,
    apply le_of_not_gt,
    intro H2,
    change b < 0 at H2,
    have H4 : b ∈ Sa,
      exact H2,
    have H5 : (b / 2) ∈ Sa,
      show b / 2 < 0,
      linarith,
    have H6 : b / 2 > b,
      linarith,
    revert H6,
    change ¬ (b / 2 > b),
    change ¬ (b < b / 2),
    apply not_lt_of_ge,
    show b / 2 ≤ b,
    apply Hb,
    assumption}
end

-- Example sheet 6 Q5
theorem Q0605 (S : set ℝ) (x : ℝ) (Hx1 : x ∈ upper_bounds S)
  (Hx2 : x ∈ S) : is_lub S x :=
begin
  split,
    assumption,
  intro a,
  intro Ha,
  apply Ha,
  assumption,
end
