import tactic.ring
-- Definition of the complexes from scratch, assuming
-- everything about the real numbers, but proving everything
-- about the complex numbers.

import data.real.basic
-- don't open data.complex.basic -- we will make our own.

-- a complex number z is a pair of reals z.re and z.im
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

-- this should probably be a simp lemma, but we never seem to need it.
theorem eta (z : ℂ) : (⟨z.re,z.im⟩ : ℂ) = z :=
begin
  cases z,
  refl,
end

theorem ext {z w : ℂ} : z.re = w.re ∧ z.im = w.im → z = w :=
begin
  cases z; cases w,
  intros,
  simp * at *,
end

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
begin
  split,
  { intro H,
    rw H,
    split;refl,
  },
  exact ext,
end

-- there is a natural map from the reals to the complexes.
instance : has_coe ℝ ℂ := ⟨λ x, ⟨x,0⟩⟩

-- I'll explain these later.
@[simp] lemma coe_re (x : ℝ) : (x : ℂ).re = x := rfl
@[simp] lemma coe_im (x : ℝ) : (x : ℂ).im = 0 := rfl

-- We define the complex number zero to be the real number zero.
protected definition zero : ℂ := (0 : ℝ)

-- We set up the notation `0`
instance : has_zero ℂ := ⟨complex.zero⟩

-- I'll explain these later.
@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl

-- We define the complex number one to be the real number one.
protected definition one : ℂ := (1 : ℝ)

-- We set up the notation `1`
instance : has_one ℂ := ⟨complex.one⟩

-- I'll explain these later.
@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl

-- We define addition on complex numbers in the usual way
protected definition add : ℂ → ℂ → ℂ :=
λ z w, ⟨z.re + w.re, z.im + w.im⟩
-- There is a reason I don't use the equation compiler here.

instance : has_add ℂ := ⟨complex.add⟩

-- OK now I'll explain the simp lemmas.

-- The strategy for proving a whole bunch of basic theorems
-- like associativity of addition, commutativity of multiplication
-- etc is "check on real and imaginary parts".
-- In Lean the strategy looks like this. 
-- First we apply ext_iff.2 to reduce the question to equality
-- of real and imaginary parts, of the form Re(blah) = Re(blah)
-- and Im(blah)=Im(blah). We then use split to make this into
-- two goals. We then use `simp` to get rid of all the occurrences
-- of `re` like (z*w).re until we are down to occurrences of things
-- like `z.re` and `z.im` for z a variable.
-- We then use `ring` to solve these basic equalities.

-- We hence need to teach `simp` how to compute the real part of
-- (z + w), for example.

-- so here are two basic facts about add which we want to be simp lemmas.
@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl
-- Note to be omitted at first reading: If I had used the equation compiler
-- when defining complex.add then these proofs would not have been rfl.

-- We define multiplication on the complex numbers in the usual way
protected definition mul : ℂ → ℂ → ℂ :=
λ z w, ⟨z.re * w.re- z.im * w.im, z.re * w.im + z.im * w.re⟩

-- We set up the notation `*`
instance : has_mul ℂ := ⟨complex.mul⟩

-- basic facts about mul which we want to be simp lemmas.
@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl

definition conjugate : ℂ → ℂ :=
λ z, ⟨z.re, -z.im⟩

@[simp] lemma conj_re (z : ℂ) : (conjugate z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conjugate z).im = -z.im := rfl

end complex

open complex

variables p q r : ℂ

meta def check_on_real_and_imag_parts : tactic unit := do
`[apply ext],
`[split],
`[all_goals {simp}],
`[all_goals {ring}]

theorem Q6a : (p + q) + r = p + (q + r) :=
by check_on_real_and_imag_parts

theorem Q6b : p * q = q * p :=
by check_on_real_and_imag_parts

theorem Q6c : conjugate p * conjugate q = conjugate (p * q) :=
by check_on_real_and_imag_parts
