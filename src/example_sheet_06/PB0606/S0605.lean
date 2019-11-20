import data.real.basic tactic.norm_num algebra.group_power

theorem Q5a1 (S : set ℝ) : (∃ x : ℝ, x ∈ lower_bounds S) 
    ↔ (∃ y : ℝ, y ∈ upper_bounds {t : ℝ | ∃ s ∈ S, t = -s }) :=
begin
split,
{ intros H,
  cases H with x Hx,
  existsi (-x),
  intro w,
  intro Hw,
  cases Hw with t Ht,
  cases Ht with u Hu,
  refine le_neg_of_le_neg _,
  apply Hx,
  rw [Hu],
  rwa neg_neg },
{ intros H,
  cases H with y Hy,
  existsi (-y),
  intro mt,
  intro Hmt,
  refine neg_le_of_neg_le _,
  apply Hy,
  existsi mt,
  existsi Hmt,
  refl
}
end 

theorem Q5a2 (S : set ℝ) (x : ℝ) : is_glb S x ↔ 
    is_lub {t : ℝ | ∃ s ∈ S, t = -s} (-x) :=
begin
split,
{ intro HSx,
  split,
  { intros ms Hms,
    refine le_neg_of_le_neg _,
    refine HSx.left _,
    cases Hms with s Hs,
    cases Hs with H1 H2,
    rw H2,
    rwa neg_neg },
  { intros b Hb,
    apply neg_le_of_neg_le _,
    apply HSx.2,
    intros c Hc,
    apply neg_le_of_neg_le _,
    apply Hb,
    existsi c,
    existsi Hc,
    refl },
},
{ intro HSx,
  split,
  { intros ms Hms,
    refine le_of_neg_le_neg _,
    refine HSx.left _,
    existsi [ms,Hms],
    refl },
  { intros b Hb,
    apply le_of_neg_le_neg _,
    apply HSx.2,
    intros c Hc,
    cases Hc with mc Hmc,
    cases Hmc with H1 H2,
    apply le_neg_of_le_neg _,
    apply Hb,
    rw H2,
    rwa neg_neg },
},
end

lemma Q5bhelper (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ ≤ x₂ :=
begin
intro H,
have Hglb1 := H.left,
have Hlb1 := Hglb1.left,
have Hglb2 := H.right,
have H1 := Hglb2.right,
exact H1 Hlb1,
end

theorem Q5b (S : set ℝ) (x₁ x₂ : ℝ) : is_glb S x₁ ∧ is_glb S x₂ → x₁ = x₂ :=
begin
intro H,
have H1 := Q5bhelper _ _ _ H,
have H2 := Q5bhelper _ _ _ ⟨H.right,H.left⟩,
exact le_antisymm H1 H2,
end

theorem Q5c :  (∀ S : set ℝ, (∃ w : ℝ, w ∈ S) → (∃ x : ℝ, x ∈ upper_bounds S) → ∃ y : ℝ, is_lub S y) 
   →   (∀ T : set ℝ, (∃ w₁ : ℝ, w₁ ∈ T) → (∃ x₁ : ℝ, x₁ ∈ lower_bounds T) → ∃ y₁ : ℝ, is_glb T y₁) :=
begin
intro H,
intro T,
have H1 := H {x : ℝ | ∃ y : ℝ, y ∈ T ∧ x = -y},
clear H,
intro J2,
cases J2 with w2 Jw2,
have H2 := H1 _,
{ intro J3,
  clear H1,
  cases J3 with w3 Jw3,
  have H3 := H2 _,
  { clear H2,
    cases H3 with y3 Hy3,
    existsi (-y3),
    split,
    { intro t,
      intro J5,
      rw neg_le,
      apply Hy3.left,
      existsi t,
      simp [J5]
    },
    intros t Ht,
    have H4 := Hy3.right,
    rw le_neg,
    apply H4,
    clear H4,
    intros u Hu,
    cases Hu with v Hv,
    rw [Hv.right],
    refine neg_le_neg _,
    apply Ht,
    exact Hv.left,
  },
  existsi (-w3),
  intros z Hz,
  rw le_neg,
  apply Jw3,
  cases Hz with u Hu,
  rw Hu.right,
  rw neg_neg,
  exact Hu.left
},
existsi (-w2),
existsi w2,
simp [Jw2],
end 
