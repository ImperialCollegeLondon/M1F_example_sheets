import data.nat.basic
import xenalib.modified_induction
import tactic.norm_num

open nat

definition meh (P Q : Prop) : (¬ Q → ¬ P) → (P → Q) := 
begin
  intros H1 H2,
  cases classical.em Q,
    assumption,
  exfalso,
  apply H1;assumption,
end

theorem Q4 (n : ℕ) (H : n > 0) : fact n < 3 ^ n ↔ n ≤ 6 :=
begin
  split, swap, -- let's do the easy case first
    intro Hn6, revert H, revert Hn6, revert n, exact dec_trivial,
  -- now the induction way
  apply meh,
  intro Htemp,
  apply not_lt_of_ge,
  replace Htemp : 7 ≤ n := lt_of_not_ge Htemp,
  revert Htemp,
  apply modified_induction, 
    -- base case
    show 7 * (6 * (5 * (4 * (3 * (2 * (1 * 1)))))) ≥ 3 ^ 7, -- just don't ask
    norm_num,
  -- inductive step
  intros d Hd7 Hd,
  refine calc 
    fact (d + 1) = (d + 1) * fact d : rfl
    ...          ≥ 3 * fact d       : nat.mul_le_mul_right _ _
    ...          ≥ 3 * 3 ^ d        : nat.mul_le_mul_left _ Hd
    ...          = 3 ^ d * 3        : by rw mul_comm,
  apply succ_le_succ,
  exact le_trans dec_trivial Hd7
end