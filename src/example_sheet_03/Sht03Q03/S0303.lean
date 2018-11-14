import analysis.real
import xenalib.real_nth_root

-- preliminary lemma

theorem pow_mono' {x : ℝ} {n : ℕ} (Hxpos : 0 < x)
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

lemma nth_root_pow_left {x : ℝ} {m n : ℕ} (Hm : 0 < m) (Hx : 0 < x) :
(nth_root x m) ^ (m * n) = x ^ n :=
begin
  rwa [pow_mul,nth_root_power],
  assumption
end

theorem Sht3Q3a : nth_root 3 (3*10^12) < nth_root 2 (2 * 10 ^ 12) :=
begin
  
end

