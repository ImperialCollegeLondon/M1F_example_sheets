import data.real.basic

-- a complex number z is a pair of reals z.re and z.im
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

-- We define addition on complex numbers in the usual way
protected definition add : ℂ → ℂ → ℂ :=
λ z w, ⟨z.re + w.re, z.im + w.im⟩

instance : has_add ℂ := ⟨complex.add⟩

protected definition mul : ℂ → ℂ → ℂ :=
λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

-- We set up the notation `*`
instance : has_mul ℂ := ⟨complex.mul⟩

definition conjugate : ℂ → ℂ :=
λ z, ⟨z.re, -z.im⟩

end complex

open complex

variables p q r : ℂ

theorem Q6a : (p + q) + r = p + (q + r) := sorry

theorem Q6b : p * q = q * p := sorry

theorem Q6c : conjugate p * conjugate q = conjugate (p * q) := sorry
