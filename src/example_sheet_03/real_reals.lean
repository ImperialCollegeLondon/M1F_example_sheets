-- just to show that the real reals satisfy all
-- the axioms I'm assuming for the fake reals!

import data.real.basic xenalib.fakereals

noncomputable instance : real' ℝ :=
{ is_field := by apply_instance,
  is_has_lt := by apply_instance,
  A1 := λ a b t H, add_lt_add_right H t,
  A2 := λ a b c, lt.trans,
  A31 := lt_trichotomy,
  A32 := λ a b,⟨λ H,⟨ne_of_lt H,not_lt_of_gt H⟩,
                     λ H,H ▸ lt_irrefl a⟩,
  A4 := λ a b,mul_pos
}