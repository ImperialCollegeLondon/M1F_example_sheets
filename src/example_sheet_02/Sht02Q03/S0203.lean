import data.rat
import data.real.basic
import tactic.ring

theorem Q3a (n : int) : (3 : ℤ) ∣ n ^ 2 → (3 : ℤ) ∣ n := begin
  intro H3n2, -- hypothesis that 3 divides n ^ 2
  -- now we write n as 3t+r with r the remainder.
  let t := n / 3, -- t is an integer; this rounds down
  let r := n % 3, -- remainder
  have Hn : r + 3 * t = n := int.mod_add_div _ _,
  -- we know 3 divides n^2; let's now prove 3 divides r^2
  have H : 3 ∣ r ^ 2,
    have Hn2 : n ^ 2 = r ^ 2 + 3 * (2 * r * t + 3 * t ^ 2),
      rw ←Hn, ring,
    -- I would now like to say that 3 ∣ n ^ 2 -> 3 ∣ r ^ 2
    -- but I can't find d ∣ n -> d ∣ (n + d * m) in the library
    -- I can only find results about n % d = (n + d * m) % d
    -- so we have to convert to this language
    rw int.dvd_iff_mod_eq_zero at H3n2,
    rw Hn2 at H3n2,
    rw int.add_mul_mod_self_left at H3n2,
    rwa int.dvd_iff_mod_eq_zero,
  -- we now have H ; 3 ∣ r ^ 2 and r is a remainder 
  -- after division by 3, so it's 0 1 or 2.
  have H0 : r ≥ 0 := int.mod_nonneg _ dec_trivial,
  have H2 : r < 3 := (show (3 : ℤ) = abs 3, by refl) ▸ int.mod_lt n dec_trivial,
  have Heasy : r = 0 ∨ r = 1 ∨ r = 2 :=
  match r, H0, H2 with
  | (int.of_nat 0), _, _ := dec_trivial
  | (int.of_nat 1), _, _ := dec_trivial
  | (int.of_nat 2), _, _ := dec_trivial
  end,
  -- now do the cases
  cases Heasy with Hr0 Hr12,
  { -- r = 0
    rw [Hr0,zero_add] at Hn,
    existsi t,
    rw Hn
  },
  cases Hr12 with Hr1 Hr2,
  { -- r = 1
    rw Hr1 at H,
    revert H,
    exact dec_trivial
  },
  { -- r = 2
    rw Hr2 at H,
    revert H,
    exact dec_trivial
  }
end


-- Two ways to formalise second part. First way does not use existence
-- of sqrt(3) (or indeed of the real numbers at all)

theorem no_rational_squared_is_three : ¬ (∃ (q : ℚ), q ^ 2 = 3) := sorry

-- second way says that the real number sqrt(3) is not in the image of the map
-- from the rationals to the reals

theorem no_rational_is_sqrt_three : ¬ (∃ (q : ℚ), (q : ℝ) = real.sqrt 3) := 
begin
  intro H,
  cases H with q Hq,
  apply no_rational_squared_is_three,
  existsi q,
  have H := (real.sqrt_prop 3).2,
  rw ←Hq at H,
  rw (show max (0 : ℝ) 3 = (3 : ℚ), by norm_num) at H,
  rw [←rat.cast_mul,rat.cast_inj] at H,
  rwa pow_two
end