import data.real.basic
import tactic.linarith

definition is_rational (r : ℝ) : Prop :=
∃ q : ℚ, (q : ℝ) = r

definition has_no_ub (S : set ℝ) := ∀ b : ℝ, ∃ s : S, b < s

def Sa : set ℝ := {x : ℝ | x < 0}

theorem Q4a_lub : is_lub Sa 0 :=
begin
  split,
  { -- 0 is an upper bound
    intro x,
    intro Hx,
    change x < 0 at Hx,
    apply le_of_lt Hx,
  },
  { intro b,
    intro Hb,
    apply le_of_not_gt,
    intro Hbneg,
    change b < 0 at Hbneg,
    unfold upper_bounds at Hb,
    dsimp at Hb,
    let H := Hb (b / 2) _,
      linarith,
    change b / 2 < 0,
    linarith
  }
end

-- this is horrible

def Sb : set ℝ := {r : ℝ | is_rational r}

theorem Q4b_no_ub : has_no_ub Sb :=
begin
  intro b,
  let q : ℚ := floor b + 1,
  refine ⟨⟨(q : ℝ),_⟩,_⟩,
    refine ⟨q,_⟩,
    refl,
  show b < q,
  suffices : (q : ℝ) = (⌊b⌋ + 1),
    rw this,
    exact lt_floor_add_one b,
  simp,
end

def Sc : set ℝ := {x : ℝ | (x + 1) ^ 2 < x ^ 2}

lemma Q0604.helper_lemma (b : ℝ) : is_lub {x : ℝ | x < b} b :=
begin
  split,
    intros x H,
    change x < b at H,
    linarith,
  intro y,
  intro Hy,
  apply le_of_not_gt,
  intro Hb,
  have Hs : (y + b) / 2 < b := by linarith,
  have H := Hy ((y + b) / 2) Hs,
  linarith,
end

theorem Q4c_lub : is_lub Sc (-1/2) :=
begin
  have H : Sc = {x : ℝ | 2 * x + 1 < 0},
  { ext,
    unfold Sc,
    change (x + 1) ^ 2 < x ^ 2 ↔ 2 * x + 1 < 0,
    rw (⟨sub_neg_of_lt,lt_of_sub_neg⟩ : (x + 1) ^ 2 < x ^ 2 ↔ (x + 1) ^ 2 - x ^ 2 < 0),
    rw (show (x + 1) ^ 2 - x ^ 2 = 2 * x + 1, by ring),
  },
  convert Q0604.helper_lemma _,
  rw H,
  ext,simp,split;intro H2;linarith,
end

-- last part still not finished

def Sd : set ℝ := {x : ℝ | is_rational x ∧ 1 < x ∧ x < 2}

theorem Q4d_lub : is_lub Sd 2 := sorry
