import data.real.irrational

open real

--lemma irrat_add_rat {x : ℝ} {y : ℚ} : irrational x → irrational (x + y) := sorry

--lemma rat_add_irrat {x : ℚ} {y : ℝ} : irrational y → irrational (x + y) := sorry

--lemma irrat_mul_rat {x : ℝ} {y : ℚ} : y ≠ 0 → irrational x → irrational (x * y) := sorry

--lemma rat_mul_irrat {x : ℚ} {y : ℝ} : x ≠ 0 → irrational y → irrational (x * y) := sorry

lemma neg_irrat {x : ℝ} : irrational x → irrational (-x) := begin
  intros H1 H2,
  apply H1,
  cases H2 with q Hq,
  existsi -q,
  rw (eq_neg_of_eq_neg Hq.symm),
  simp
end

--lemma e_irrat : irrational (exp 1) := sorry

/-

Other ideas: sqrt(p) is irrational if p is prime
There exists no p-adic number whose square has odd p-adic valuation
sqrt(n) is irrational if there exists some prime p such that the p-adic
valuation of n is odd

-/