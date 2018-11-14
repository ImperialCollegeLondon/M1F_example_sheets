import analysis.real
variables {x t : ℝ}

noncomputable def abv (x : ℝ) := if x ≥ 0 then x else -x

theorem Q0305a (Ht : t > 0) : abv x < t ↔ -t < x ∧ x < t :=
begin
  unfold abv,
  split_ifs;split,
  { intro H,
    split, swap, assumption,
    apply lt_of_lt_of_le _ h,
    rwa [neg_lt,neg_zero]
  },
  { rintro ⟨H1,H2⟩,
    exact H2
  },
  { intro H,
    split, rwa neg_lt,
    apply lt_trans _ Ht,
    exact lt_of_not_ge h, 
  },
  { rintro ⟨H1,H2⟩,
    rwa neg_lt,
  }
end


theorem Q0305b : abv (x + 1) < 3 ↔ -4 < x ∧ x < 2 :=
begin
  rw Q0305a,
    swap, norm_num,
  rw ←sub_lt_iff_lt_add,
  rw (show (-(3 : ℝ) - 1 = -4), by norm_num),
  rw ←lt_sub_iff_add_lt,
  rw (show ((3 : ℝ) - 1 = 2), by norm_num),
end

-- change the RHS to the correct explicit range
theorem Q0305c : abv (x - 2) < abv (x - 4) ↔ x < 3 :=
begin
  
end