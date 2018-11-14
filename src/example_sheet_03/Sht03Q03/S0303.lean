import analysis.real
import xenalib.real_nth_root
import tactic.norm_num
import tactic.explode

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

-- end of Q3a

-- Q3b

-- nat.pow_lt_pow_of_lt_right :
-- ∀ {x : ℕ}, x > 1 → ∀ {i j : ℕ}, i < j → x ^ i < x ^ j

variable (x : ℝ) -- or [linear_ordered_field]
theorem pow_lt_pow_of_lt {i j : ℕ} (Hx : x > 1) (Hij : i < j) : x^i < x^j :=
begin
  sorry
end

open nat

theorem nat.pow_lt_pow_of_lt_right' {x : ℕ} (H : x > 1) {i j : ℕ} (h : i < j) : x^i < x^j :=
begin
  have xpos := lt_of_succ_lt H,
  refine lt_of_lt_of_le _ (pow_le_pow_of_le_right xpos h),
  rw [← mul_one (x^i), nat.pow_succ],
  exact nat.mul_lt_mul_of_pos_left H (pos_pow_of_pos _ xpos)
end

/- Mario proof -/
variables {α : Type*} [linear_ordered_semiring α]
theorem pow_lt_pow {a : α} {n m : ℕ} (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
lt_of_lt_of_le
  ((lt_mul_iff_one_lt_left (pow_pos (lt_trans zero_lt_one ha) _)).2 ha)
  (pow_le_pow (le_of_lt ha) h)

theorem pow_lt_pow' {a : α} {n m : ℕ} (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
begin
  apply lt_of_lt_of_le,
  { exact ((lt_mul_iff_one_lt_left (pow_pos (lt_trans zero_lt_one ha) _)).2 ha)},
  exact (pow_le_pow (le_of_lt ha) h)
end

theorem pow_lt_pow'' {a : α} {n m : ℕ} (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
begin
  apply lt_of_lt_of_le,
  { refine (lt_mul_iff_one_lt_left _).2 ha,
    refine pow_pos _ _,
    -- got it
    exact lt_trans zero_lt_one ha
  },
  { refine pow_le_pow _ h, -- dirty trick?
    exact le_of_lt ha
  }
end

-- I want a button which puts
--set_option pp.all true
-- on and off

-- I've made them reals to keep with the theme of the sheet
-- change the inequality if you think it goes the other way
theorem Sht3Q3b : (10000 : ℝ) ^ 100 < (100 : ℝ) ^ 10000 := begin
  rw (show 10000 = 100 * 100, by norm_num),
  rw pow_mul,
  -- next line doesn't work

  -- apply pow_mono (by norm_num) (dec_trivial),
  
  -- but this variant does
  refine pow_mono (by norm_num) (dec_trivial) _,
  rw (show (10000 : ℝ) = 100 ^ 2, by norm_num),
  exact pow_lt_pow (by norm_num) dec_trivial,
end

-- replace with the right explicit real number
theorem Sht3Q03ci : nth_root (2 ^ 22) 2 = (0 : ℝ) := sorry

-- replace with the right explicit real number
theorem Sht3Q03cii : nth_root (2 ^ 2 ^ 22) 2 = (0 : ℝ) := sorry



