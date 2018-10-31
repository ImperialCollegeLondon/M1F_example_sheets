import xenalib.fakereals
import xenalib.M1F_chapter2_lemmas
import tactic.ring

variables {R : Type} [real' R] {x y : R}

open real'

theorem M1F_Sht03Q02a (Hx : 0 < x) (Hy : y < 0) : x * y < 0 := 
begin
  convert mul_left_pos_lt_of_lt Hy Hx,
  rw mul_zero
end

theorem M1F_Sht03Q02b (Hx : x < 0) (Hy : y < 0) : 0 < x * y :=
begin
  have Hx2 : 0 < -x := neg_pos_of_neg' Hx,
  have Hy2 : 0 < -y := neg_pos_of_neg' Hy,
  have Hnegneg : x * y = (-x) * (-y),
    simp,
  rw Hnegneg,
  exact A4 Hx2 Hy2
end

theorem M1F_Sht03Q02c (Hxy : x * y = 0) : x = 0 ∨ y = 0 :=
begin
  rcases A31 x 0 with Hnegx | Hzerox | Hposx;
  rcases A31 y 0 with Hnegy | Hzeroy | Hposy,
  { exfalso,
    have H : 0 < x * y := M1F_Sht03Q02b Hnegx Hnegy,
    exact ne_of_lt H Hxy.symm
  },
  { right, assumption},
  { exfalso,
    have H : x * y < 0 := mul_comm y x ▸ M1F_Sht03Q02a Hposy Hnegx,
    exact ne_of_lt H Hxy,
  },
  { left, assumption},
  { left, assumption},
  { left, assumption},
  { exfalso,
    have H : x * y < 0 := M1F_Sht03Q02a Hposx Hnegy,
    exact ne_of_lt H Hxy,
  },
  {right, assumption},
  { exfalso,
    have H : x * y > 0 := A4 Hposx Hposy,
    exact ne_of_lt H Hxy.symm,
  },
end

definition unique_pos_sqrt (x : R) :=
∃! y : R, 0 < y ∧ y * y = x

lemma real'.two_ne_zero : (2 : R) ≠ 0 :=
begin
  apply ne.symm,
  apply real'.ne_of_lt,
  apply A2 one_pos,
  convert A1 one_pos,
  simp
end

theorem M1F_Sht03Q02d (H : 0 < x → unique_pos_sqrt x) : 
0 < x → ∃ z1 z2 : R, z1 ≠ z2 ∧ z1 * z1 = x ∧ z2 * z2 = x 
  ∧ ∀ z : R, z * z = x → z = z1 ∨ z = z2 :=
begin
  intro Hx,
  rcases H Hx with ⟨y,⟨Hypos,Hysq⟩,Hy2⟩,
  existsi y,
  existsi -y,
  split,
  { intro Hyneg,
    have H2y : 2 * y = 0,
      rw two_mul,
      conv in y begin
         rw Hyneg,
      end,
      simp,
    cases M1F_Sht03Q02c H2y with H20 Hy0,
      exact real'.two_ne_zero H20,
    exact ne_of_lt Hypos Hy0.symm
  },
  split, assumption,
  split,
  { rw ←Hysq,
    simp,
  },
  intros z Hz,
  rw ←Hysq at Hz,
  replace Hz := sub_eq_zero_of_eq Hz,
  have Hzy : z * z - y * y = (z - y) * (z + y) := by ring,
  rw Hzy at Hz,
  cases M1F_Sht03Q02c Hz with H1 H2,
  { left,
    exact eq_of_sub_eq_zero H1
  },
  { right,
    exact eq_neg_of_add_eq_zero H2
  }
end
