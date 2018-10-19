import algebra.group_power data.real.basic

def countable_union_from_zero {α : Type} (X : nat → set α) :=
{t : α | exists i, t ∈ X i}

def countable_union_from_one {α : Type} (X : nat → set α) :=
{t : α | exists i, 0 < i ∧ t ∈ X i}

def countable_intersection_from_one {α : Type} (X : nat → set α) :=
{t : α | ∀ i, 0 < i → t ∈ X i}

def Q0201a_sets (n : ℕ) : set ℝ := {x | ↑n ≤ x ∧ x < (n+1)}

theorem Q0201a : countable_union_from_zero Q0201a_sets = ??? := sorry

def Q0201b_sets (n : ℕ) : set ℝ := {x | 1/(↑n) ≤ x ∧ x ≤ 1}

theorem Q0201b : countable_union_from_one Q0201b_sets = ??? := sorry 

def Q0201c_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

theorem Q0201c : countable_union_from_one Q0201c_sets = ??? := sorry

def Q0201d_sets (n : ℕ) : set ℝ := {x | -↑n < x ∧ x < n}

theorem Q0201d : countable_intersection_from_one Q0201d_sets = ??? := sorry
