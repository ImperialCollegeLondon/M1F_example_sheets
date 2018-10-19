import algebra.group_power data.real.basic

def countable_union_from_zero {α : Type} (X : nat → set α) :=
{t : α | exists i, t ∈ X i}

def countable_union_from_one {α : Type} (X : nat → set α) :=
{t : α | exists i, 0 < i ∧ t ∈ X i}

def countable_intersection_from_one {α : Type} (X : nat → set α) :=
{t : α | ∀ i, 0 < i → t ∈ X i}

def Q0201a_sets (n : ℕ) : set ℝ := {x | ↑n ≤ x ∧ x < (n+1)}

theorem Q0201a : countable_union_from_zero Q0201a_sets = {x | 0 ≤ x} := 
begin
  apply set.subset.antisymm,
  { -- union ⊆ {x | 0 ≤ x}
    intro x,
    show (∃ i : ℕ, ↑i ≤ x ∧ x < (i + 1)) → 0 ≤ x,
    intro H,
    cases H with i Hi,
    apply le_trans _ Hi.left,
    simp,
  },
  { -- {x | 0 ≤ x} ⊆ union
    intros x Hx,
    change 0 ≤ x at Hx,
    change ∃ i : ℕ, ↑i ≤ x ∧ x < (i + 1),
    let m := floor x, -- unfortunately an integer, not a natural!
    have Hm : 0 ≤ m,
      convert floor_mono Hx,
      simp,
    existsi int.nat_abs m,
    suffices : (((int.nat_abs m) : ℤ) : ℝ) ≤ x ∧ x < ((int.nat_abs m) : ℤ) + 1,
      simpa,
    rw int.nat_abs_of_nonneg Hm,
    exact ⟨floor_le x,lt_floor_add_one x⟩,
  },
end

def Q0201b_sets (n : ℕ) : set ℝ := {x | 1/(↑n) ≤ x ∧ x ≤ 1}

theorem Q0201b : countable_union_from_one Q0201b_sets = { x | 0 < x ∧ x ≤ 1} :=
begin
  unfold countable_union_from_one,
  apply set.subset.antisymm,
  { -- this branch shows the union ⊆ (0,1]
    rintro x ⟨i,Hi,Hx⟩,
    change 1/(i : ℝ) ≤ x ∧ x ≤ 1 at Hx,
    split,
    { apply lt_of_lt_of_le _ Hx.1,
      apply one_div_pos_of_pos,
      simp [Hi]},
    exact Hx.2
  },
  { rintro x ⟨H0,H1⟩,
    -- now need a natual i > 0 with 1 / i <= x
    let m := ceil (1 / x), -- an integer!
    have Hm : 0 < m,
      -- 0 < 1/x <= m
      exact int.cast_lt.1 (lt_of_lt_of_le (one_div_pos_of_pos H0) (le_ceil (1/x))),
    let i := int.nat_abs m, -- take the absolute value!
    have Hi : m = i := int.eq_nat_abs_of_zero_le (le_of_lt Hm),
    -- m is finally i, with i a natural
    existsi i,
    split,
      exact int.coe_nat_lt.1 (Hi ▸ Hm),
    -- now need to show x in [1/i,1]
    change 1/(i : ℝ) ≤ x ∧ x ≤ 1,
    split,
    { -- 1/i <= x
      apply one_div_le_of_one_div_le_of_pos H0,
      change 1/x ≤ (i : ℤ),
      rw ←Hi,
      exact le_ceil (1/x)
    },
  exact H1
  }
end

def Q0201c_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

theorem Q0201c : countable_union_from_one Q0201c_sets = set.univ :=
begin
  apply set.eq_univ_of_forall,
  intro x,
  let m := ceil (1 + abs x), -- an integer
  have Hm : 1 ≤ m := int.cast_le.1 
    (le_trans (le_add_of_nonneg_right $ abs_nonneg _)
      (le_ceil (1 + abs x)) : (1 : ℝ) ≤ m),
  let i := int.nat_abs m, -- the natural we want
  have Hi : m = i := int.eq_nat_abs_of_zero_le (le_of_lt Hm),
  existsi i,
  split,
    exact int.coe_nat_lt.1 (Hi ▸ lt_of_lt_of_le zero_lt_one Hm),
  split,
  { rw neg_lt,
    show -x < (i : ℤ),
    rw ←Hi,
    refine lt_of_lt_of_le _ (le_ceil _),
    refine lt_of_le_of_lt (neg_le_abs_self x) _,
    exact lt_add_of_pos_left _ zero_lt_one
  },
  { show x < (i : ℤ),
    rw ←Hi,
    refine lt_of_lt_of_le _ (le_ceil _),
    refine lt_of_le_of_lt (le_abs_self x) _,
    exact lt_add_of_pos_left _ zero_lt_one
  }
end

def Q0201d_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

theorem Q0201d : countable_intersection_from_one Q0201d_sets = {x | -1 < x ∧ x < 1} :=
begin
  apply set.subset.antisymm,
  { -- intersection ⊆ (-1,1)
    intros x Hx,
    exact Hx 1 zero_lt_one,
  },
  { -- (-1,1) ⊆ intersection
    rintros x ⟨Hm,Hp⟩ i Hi,
    split,
    { refine lt_of_le_of_lt _ Hm,
      apply neg_le_neg,
      show ((1 : ℕ) : ℝ) ≤ i,
      rw nat.cast_le,
      exact Hi
    },
    { refine lt_of_lt_of_le Hp _,
      show ((1 : ℕ) : ℝ) ≤ i,
      rw nat.cast_le,
      exact Hi     
    }
  }
end
