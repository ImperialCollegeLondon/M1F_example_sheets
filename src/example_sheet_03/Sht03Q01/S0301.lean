import xenalib.fakereals tactic.interactive tactic.rcases

open real'

theorem M1F_Sht03Q01 (R : Type) [real' R] (x y : R) : 0 < x ∧ 0 < y → 0 < (x + y) :=
begin
  rintro ⟨Hx,Hy⟩,
  have H : y < x + y,
    convert A1 Hx,
    rw zero_add,
  exact A2 Hy H   
end
