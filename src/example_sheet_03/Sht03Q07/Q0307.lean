import example_sheet_03.Sht03Q06.Q0306

namespace complex

-- coercion from reals to complexes
instance : has_coe ℝ ℂ := ⟨λ x, ⟨x,0⟩⟩

protected definition one : ℂ := ⟨1,0⟩
instance : has_one ℂ := ⟨complex.one⟩

definition I : ℂ := ⟨0,1⟩

protected definition neg : ℂ → ℂ := λ z, ⟨-z.re, -z.im⟩

instance : has_neg ℂ := ⟨complex.neg⟩

protected def pow (z : ℂ) : ℕ → ℂ
| 0 := 1
| (n + 1) := z * pow n

instance : has_pow ℂ ℕ := ⟨complex.pow⟩

end complex

-- we now have enough notation to state the question!

open complex

variable z : ℂ

theorem Q7 (H : z ^ 2 = -1) : z = I ∨ z = -I := sorry
