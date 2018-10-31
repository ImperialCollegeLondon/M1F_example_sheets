import xenalib.fakereals tactic.interactive

namespace real'

variables {R : Type} [real' R] {x y a b c : R}

-- lemma 2.1
lemma neg_lt_neg_of_gt (H : a < b) : -b < -a :=
begin
  convert (A1 H : a + (-a + -b) < _),
    rw [←add_assoc,add_neg_self,zero_add],
    rw [add_comm,add_assoc,neg_add_self,add_zero]
end

-- lemma 2.2
lemma neg_pos_of_neg' (H : x < 0) : -x > 0 :=
begin
  convert neg_lt_neg_of_gt H,
  simp,
end

-- lemma 2.5
lemma mul_left_pos_lt_of_lt (Hxy : x < y) (Hc : c > 0) :
c * x < c * y :=
begin
  have Hyx : 0 < (y - x),
    rw sub_eq_add_neg,
    convert A1 Hxy,
    simp,
  have Hcyx : 0 < c * (y - x) := A4 Hc Hyx,
  rw mul_sub at Hcyx,
  convert (A1 Hcyx : 0 + c * x < _),
    simp,
    simp
end

-- corollary 2.8
theorem one_pos {R : Type} [real' R] : 0 < (1 : R) :=
begin
  cases (A31 (0 : R) 1) with H1pos H1nonpos,
    assumption,
  cases H1nonpos with H1zero H1neg,
    exfalso,
    apply (zero_ne_one : (0 : R) = 1 → false),
    assumption,
  have H : (1 : R) + (-1) < 0 + (-1) := A1 H1neg,
    rw [add_neg_self,zero_add] at H,
  have H2 : (-1 : R) * (-1) > 0 := A4 H H,
  rw [←neg_eq_neg_one_mul,neg_neg] at H2,
  exact H2,
end

end real'