import analysis.real
import xenalib.real_nth_root
import tactic.norm_num

-- preliminary lemma

open real 

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

lemma nth_root_pow_right {x : ℝ} {m n : ℕ} (Hm : 0 < m) (Hx : 0 < x) :
(nth_root x m) ^ (m * n) = x ^ n :=
begin
  rwa [pow_mul,nth_root_pow_self],
  assumption
end

lemma nth_root_pow_left {x : ℝ} {m n : ℕ} (Hm : 0 < m) (Hx : 0 < x) :
(nth_root x m) ^ (n * m) = x ^ n := by rw [mul_comm,nth_root_pow_right Hm Hx]

lemma nth_root_pow {x : ℝ} {m n : ℕ} (Hm : 0 < m) (Hx : 0 < x) :
(nth_root x m) ^ n = nth_root (x ^ n) m :=
begin
  apply nth_root_unique (pow_pos Hx _) (pow_pos (nth_root_pos Hx Hm) _) Hm _,
  rw [←pow_mul,nth_root_pow_left Hm Hx],
end

-- If I hover over the first nth_root_pos below, I don't get a transient
-- hover box with the definition of the function. If I hover over
-- the second, I do.
theorem Sht3Q3a : nth_root 2 (2 * 10 ^ 12) < nth_root 3 (3 * 10 ^ 12) :=
begin
  -- could I have got away with something equally neat but only one line?
  have H3 : 0 < (3 : ℝ) := by norm_num,
  have H3T : 0 < 3 * 10 ^ 12 := dec_trivial,
  have H2 : 0 < (2 : ℝ) := by norm_num,
  have H2T : 0 < 2 * 10 ^ 12 := dec_trivial,
  apply lt_of_pow_lt (nth_root_pos H2 H2T) (nth_root_pos H3 H3T),
  rw nth_root_pow_self H2 H2T,
  -- why does this line cause chaos?
  -- apply lt_of_pow_lt H3 (pow_pos (nth_root_pos H2 H2T) (2 * 10 ^ 12)),
  apply lt_of_pow_lt H2 (pow_pos (nth_root_pos H3 H3T) _),
  swap, exact (3 * 10 ^ 12), -- ??
  rw [←pow_mul,nth_root_pow_left H3T H3,pow_mul,pow_mul],
  exact pow_mono (by norm_num) dec_trivial (by norm_num),
end

-- I've made them reals to keep with the theme of the sheet
-- change the inequality if you think it goes the other way
theorem Sht3Q3b : (100 : ℝ) ^10000 < 10000^100 := sorry 

-- replace with the right explicit real number
theorem Sht3Q03ci : nth_root (2 ^ 22) 2 = (0 : ℝ) := sorry

-- replace with the right explicit real number
theorem Sht3Q03cii : nth_root (2 ^ 2 ^ 22) 2 = (0 : ℝ) := sorry


-- found in original question
--theorem pow_lt_pow_of_lt {x i j : ℕ} : x > 1 → i < j → x^i < x^j :=
