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

lemma nth_root_pow_left' {x : ℝ} {m n : ℕ} (Hn : 0 < n): --(Hm : 0 < m) (Hx : 0 < x) :
(nth_root x (m * n)) ^ n = nth_root x m :=
begin
  -- first do junk x<=0 case
  cases (le_or_gt x 0) with Hle0 Hx,  
  { unfold nth_root,
    unfold log,
    split_ifs,
      exfalso, apply not_lt_of_ge Hle0, exact h,
    rw [zero_div,zero_div,exp_zero,one_pow],
  },
  -- now do junk m = 0 case
  cases m with m,
    simp [nth_root],
  -- now do only case anyone will ever use
  refine nth_root_unique Hx _ (nat.succ_pos _) _,
    exact pow_pos (nth_root_pos Hx (mul_pos (nat.succ_pos _) Hn)) _,
  rw [←pow_mul,mul_comm,nth_root_pow_self Hx],
  refine mul_pos Hn (nat.succ_pos _),
end

lemma nth_root_pow_right' {x : ℝ} {m n : ℕ} (Hn : 0 < n): --(Hm : 0 < m) (Hx : 0 < x) :
(nth_root x (n * m)) ^ n = nth_root x m :=
begin
  rw mul_comm,
  exact nth_root_pow_left' Hn,
end

lemma nth_root_pow {x : ℝ} {m n : ℕ} (Hm : 0 < m) (Hx : 0 < x) :
(nth_root x m) ^ n = nth_root (x ^ n) m :=
begin
  apply nth_root_unique (pow_pos Hx _) (pow_pos (nth_root_pos Hx Hm) _) Hm _,
  rw [←pow_mul,nth_root_pow_left Hm Hx],
end

lemma nth_root_pow_self' {x : ℝ} {n : ℕ} (Hx : 0 < x) (Hn : 0 < n):
nth_root (x ^ n) n = x :=
(nth_root_unique (pow_pos Hx _) Hx Hn rfl).symm


lemma nth_root_pow_left'' {x : ℝ} {m n : ℕ} (Hn : 0 < n) (Hx : 0 < x) :
nth_root (x ^ (m * n)) n = x ^ m :=
begin
  rw pow_mul,
  refine nth_root_pow_self' (pow_pos Hx _) Hn,
end

lemma nth_root_pow_right'' {x : ℝ} {m n : ℕ} (Hn : 0 < n) (Hx : 0 < x) :
nth_root (x ^ (n * m)) n = x ^ m :=
begin
  rw mul_comm,
  exact nth_root_pow_left'' Hn Hx,
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
    swap, exact (2 * 10 ^ 12), -- ??
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

/- Mario proof -/
variables {α : Type*} [linear_ordered_semiring α]
theorem pow_lt_pow {a : α} {n m : ℕ} (ha : 1 < a) (h : n < m) : a ^ n < a ^ m :=
lt_of_lt_of_le
  ((lt_mul_iff_one_lt_left (pow_pos (lt_trans zero_lt_one ha) _)).2 ha)
  (pow_le_pow (le_of_lt ha) h)

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
theorem Sht3Q03ci : nth_root (2 ^ 22) 2 = 2 ^ 11 :=
begin
  show nth_root (2 ^ (2 * 11)) 2 = 2 ^ 11,
  exact nth_root_pow_right'' (by norm_num) (by norm_num),
end

--set_option pp.all true
-- replace with the right explicit real number
theorem Sht3Q03cii : nth_root (2 ^ 2 ^ 22) 2 = 2 ^ 2 ^ 21 :=
begin
  change nth_root (2 ^ 2 ^ (21 + 1)) 2 = 2 ^ 2 ^ 21,
  rw nat.pow_succ 2 21,
  rw nth_root_pow_left'' _ _,
    norm_num,
  norm_num
end


