--import algebra.group_power tactic.norm_num algebra.big_operators
import tactic.ring

def Fib : ℕ → ℕ
| 0 := 0 -- question only defines F_n for n>=1 so set F_0 = junk value
| 1 := 1
| 2 := 1
| (n + 3) := Fib (n + 1) + Fib (n + 2)

def is_even (n : ℕ) : Prop := ∃ k, n = 2 * k
def is_odd (n : ℕ) : Prop := ∃ k, n = 2 * k + 1

lemma even_of_even_add_even (a b : ℕ) : is_even a → is_even b → is_even (a+b) :=
begin
  intros Ha Hb,
  cases Ha with k Hk,
  cases Hb with l Hl,
  existsi k+l,
  simp [Hk,Hl,mul_add],
end

lemma odd_of_odd_add_even {a b : ℕ} : is_odd a → is_even b → is_odd (a+b) :=
begin
  intros Ha Hb,
  cases Ha with k Hk,
  cases Hb with l Hl,
  existsi k+l,
  simp [Hk,Hl,mul_add],
end

lemma odd_of_even_add_odd {a b : ℕ} : is_even a → is_odd b → is_odd (a+b) :=
λ h1 h2, (add_comm b a) ▸ (odd_of_odd_add_even h2 h1)

lemma even_of_odd_add_odd {a b : ℕ} : is_odd a → is_odd b → is_even (a+b) :=
begin
  intros Ha Hb,
  cases Ha with k Hk,
  cases Hb with l Hl,
  existsi k+l+1,
  rw [Hk,Hl,mul_add,mul_add],
  change 2 with 1+1,
  simp [mul_add,add_mul],
end

-- starting at 0 would have been such a better idea
theorem Q0501a : ∀ n : ℕ, n ≥ 1 →
  is_odd (Fib (3 * n - 2)) ∧ is_odd (Fib (3 * n - 1)) ∧ is_even (Fib (3 * n)) :=
begin
  intros n Hn,
  cases n with m, cases Hn, -- stupid n = 0 case
  clear Hn,
  induction m with d Hd,
    -- n = 1 case
    exact ⟨⟨0,rfl⟩,⟨0,rfl⟩,⟨1,rfl⟩⟩,
  -- general case
  rcases Hd with ⟨H3dp1,H3dp2,H3dp3⟩,
  -- one could tidy up now, with
  --rw (show 3 * (nat.succ d) - 2 = 3 * d + 1, by ring) at H3dp1,
  --rw (show 3 * (nat.succ d) - 1 = 3 * d + 2, by ring) at H3dp2,
  --rw (show 3 * (nat.succ d) = 3 * d + 3, by ring) at H3dp3,
  --but this is a false economy, all these things are true by refl
  -- and Lean can just work them out by itself. 
  -- We can just go straight to the proof.
  have H3dp4 : is_odd (Fib (3 * d + 4)),
    rw [Fib], exact odd_of_odd_add_even H3dp2 H3dp3,
  have H3dp5 : is_odd (Fib (3 * d + 5)),
    rw [Fib], exact odd_of_even_add_odd H3dp3 H3dp4,
  have H3dp6 : is_even (Fib (3 * d + 6)),
    rw [Fib], exact even_of_odd_add_odd H3dp4 H3dp5,
  rw (show 3 * (nat.succ (nat.succ d)) - 2 = 3 * d + 4, by ring),
  exact (⟨H3dp4,H3dp5,H3dp6⟩ : _ ∧ _ ∧ _)
end

theorem Q0501b : is_odd (Fib (2018)) :=
begin
  have H : 2018 = 3 * 673 - 1 := dec_trivial,
  rw H,
  exact (Q0501a _ dec_trivial).right.left
end
