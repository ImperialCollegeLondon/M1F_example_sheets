import xenalib.fakereals
import xenalib.M1F_chapter2_lemmas

variables {R : Type} [real' R] (x y : R)

theorem M1F_Sht03Q02a (Hx : 0 < x) (Hy : y < 0) : x * y < 0 := sorry

theorem M1F_Sht03Q02b (Hx : x < 0) (Hy : y < 0) : 0 < x * y := sorry

theorem M1F_Sht03Q02c (Hxy : x * y = 0) : x = 0 ∨ y = 0 := sorry

definition unique_pos_sqrt (x : R) :=
∃! y : R, 0 < y ∧ y * y = x

theorem M1F_Sht03Q02d (H : 0 < x → unique_pos_sqrt x) : 
0 < x → ∃ z1 z2 : R, z1 ≠ z2 ∧ z1 * z1 = x ∧ z2 * z2 = x 
  ∧ ∀ z : R, z * z = x → z = z1 ∨ z = z2 := sorry