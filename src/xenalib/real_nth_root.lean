import analysis.real
import analysis.exponential

open real

noncomputable definition nth_root (x : ℝ) (n : ℕ) : ℝ :=
exp (log x / n)

lemma nth_root_pos {x : ℝ} {n : ℕ} (Hxpos : x > 0) (Hnpos : n > 0) : nth_root x n > 0 := exp_pos _

theorem exp_mul {x : ℝ} : ∀ n : ℕ, exp (n * x) = (exp x) ^ n
| 0 := by simp
| (nat.succ n) := by rw [pow_succ', nat.cast_add_one, add_mul, exp_add, ←exp_mul, one_mul]

theorem nth_root_power {x : ℝ} {n : ℕ} (Hxpos : 0 < x) (Hnpos : 0 < n) : (nth_root x n) ^ n = x :=
  begin
    rw [nth_root, ←exp_mul, mul_div_cancel', exp_log Hxpos],
    rw [nat.cast_ne_zero], apply ne_of_gt Hnpos,
  end

lemma nth_power_mono {x : ℝ} {n : ℕ} (Hxpos : 0 < x)
  (Hnpos : 0 < n) (y : ℝ) : x < y → x ^ n < y ^ n :=
begin
  cases n with d Hd,
    cases Hnpos,
  intro Hxy,
  clear Hnpos,
  induction d with e He,
    rwa [pow_one,pow_one],
  rw [pow_succ,pow_succ y],
  apply mul_lt_mul,
        assumption,
      exact le_of_lt He,
    apply pow_pos Hxpos,
  exact le_of_lt (lt_trans Hxpos Hxy),
end

theorem nth_root_unique {x y : ℝ} {n : ℕ} (Hxpos : 0 < x) (Hypos : 0 < y)
  (Hnpos : 0 < n) : y ^ n = x → y = nth_root x n :=
begin
  intro Hyn,
  rw ←nth_root_power Hxpos Hnpos at Hyn,
  have H1 := lt_or_ge y (nth_root x n),
  cases H1 with Hlt Hge,
    exfalso,
    revert Hyn,
    apply ne_of_lt,
    exact nth_power_mono Hypos Hnpos (nth_root x n) Hlt,
  change nth_root x n ≤ y at Hge,
  cases (eq_or_lt_of_le Hge) with Heq Hlt,
    rw Heq,
  exfalso,
  revert Hyn,
  apply ne_of_gt,
  exact nth_power_mono (nth_root_pos Hxpos Hnpos) Hnpos y Hlt,
end

