import data.real.basic

definition is_rational (r : ℝ) : Prop :=
∃ q : ℚ, (q : ℝ) = r

definition has_no_ub (S : set ℝ) := ∀ b : ℝ, ∃ s : S, b < s

-- Each of the sets in this question is non-empty. Either compute
-- the LUB and replace 37 with your answer and prove the result,
-- or prove that there are no upper bounds at all.

def Sa : set ℝ := {x : ℝ | x < 0}

-- choose one; replace 37 if necessary

-- 37 is least upper bound
theorem Q4a_lub : is_lub Sa 37 := sorry

-- there are no upper bounds
theorem Q4a_no_ub : has_no_ub Sa := sorry

def Sb : set ℝ := {r : ℝ | is_rational r}

theorem Q4b_lub : is_lub Sb 37 := sorry

theorem Q4b_no_ub : has_no_ub Sb := sorry

def Sc : set ℝ := {x : ℝ | (x + 1) ^ 2 < x ^ 2}

theorem Q4c_lub : is_lub Sc 37 := sorry

theorem Q4c_no_ub : has_no_ub Sc := sorry

def Sd : set ℝ := {x : ℝ | is_rational x ∧ 1 < x ∧ x < 2}

theorem Q4d_lub : is_lub Sd 37 := sorry

theorem Q4d_no_ub : has_no_ub Sd := sorry