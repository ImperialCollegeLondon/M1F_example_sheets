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

theorem Q4c_lub : is_lub Sc (-1/2) :=
begin
  have H : Sc = {x : ℝ | 2 * x + 1 < 0},
  { ext,
    unfold Sc,
    change (x + 1) ^ 2 < x ^ 2 ↔ 2 * x + 1 < 0,
    sorry
  },
  split,
  sorry,sorry,
end


theorem Q3c_no_ub : has_no_ub Sc := sorry

def Sd : set ℝ := {x : ℝ | is_rational x ∧ 1 < x ∧ x < 2}

theorem Q3d_lub : is_lub Sd 37 := sorry

theorem Q3d_no_ub : has_no_ub Sd := sorry