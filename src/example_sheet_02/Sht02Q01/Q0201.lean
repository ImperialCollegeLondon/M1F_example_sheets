import algebra.group_power data.real.basic

def countable_union_from_zero {α : Type} (X : nat → set α) :=
{t : α | exists i, t ∈ X i}

def countable_union_from_one {α : Type} (X : nat → set α) :=
{t : α | exists i, 0 < i ∧ t ∈ X i}

def countable_intersection_from_one {α : Type} (X : nat → set α) :=
{t : α | ∀ i, 0 < i → t ∈ X i}

def Q0201a_sets (n : ℕ) : set ℝ := {x | ↑n ≤ x ∧ x < (n+1)}

-- replace with the right set
theorem Q0201a : countable_union_from_zero Q0201a_sets = {x : ℝ | x = 37} := sorry

def Q0201b_sets (n : ℕ) : set ℝ := {x | 1/(↑n) ≤ x ∧ x ≤ 1}

-- replace with the right set
theorem Q0201b : countable_union_from_one Q0201b_sets = {x : ℝ | x = 37} := sorry 

def Q0201c_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

-- replace with the right set
theorem Q0201c : countable_union_from_one Q0201c_sets = {x : ℝ | x = 37} := sorry

def Q0201d_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

-- replace with the right set
theorem Q0201d : countable_intersection_from_one Q0201d_sets = {x : ℝ | x = 37} := sorry
