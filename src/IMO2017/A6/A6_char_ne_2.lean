import
  IMO2017.A6.A6_general



/-
2.  Solution for the case char(F) ≠ 2
-/

---- Injectivity result and characterization result for char F ≠ 2
lemma fn_lem2_1 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x : F, f (x - 1) = f x + 1 :=
begin
  intros f h h0 x,
  rw [← sub_eq_iff_eq_add, ← fn_lem4_1 F f h h0, sub_add_cancel],
end

lemma fn_lem2_2 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ (x : F), f (f x * 2) + f x + 1 = f (-x) :=
begin
  intros f h h0 x,
  suffices : f (-1) = 2,
  { have h1 := h x (-1),
    rwa [← sub_eq_add_neg, fn_lem2_1 F f h h0, mul_neg_one, ← add_assoc, this] at h1, },
  rw [← sub_left_inj, ← fn_lem4_1 F f h h0, neg_add_self, h0],
  norm_num,
end

lemma fn_lem2_3 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x y : F, f x = f y → f (x - y) = f (-(x - y)) :=
begin
  intros f h h0 x y h1,
  have h2 : f (-x) = f (-y) := by rw [← fn_lem2_2 F f h h0, ← fn_lem2_2 F f h h0, h1],
  have h3 := h x (-y),
  rw [mul_neg, ← neg_mul, ← h (-x) y, h1, h2, mul_comm, add_right_inj] at h3,
  rwa [sub_eq_add_neg, neg_add, neg_neg],
end

lemma fn_lem2_4 (char_ne_2 : ring_char F ≠ 2) : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x : F, f x = f (-x) → x = 0 :=
begin
  intros f h h0 x h1,
  have X : f ≠ 0,
  { intros h2; subst h2,
    simp at h0,
    exact h0, },
  have h2 := fn_lem2_2 F f h h0 x,
  rw [← h1, add_assoc, ← eq_sub_iff_add_eq, sub_add_cancel'] at h2,
  rw [← add_eq_zero_iff_eq_neg, ← fn_lem2_1 F f h h0, fn_thm3 F f h X, sub_eq_iff_eq_add'] at h2,
  have char_prop : 2 ≠ (0 : F),
  { intros h3,
    have h4 : (-1 : F) = 1,
    { calc (-1 : F) = 0 - 1 : by rw zero_sub
      ... = 2 - 1 : by rw ← h3
      ... = 1 : by norm_num, },
    rw neg_one_eq_one_iff at h4,
    contradiction, },
  have h3 : f x = 1,
  { calc f x = (f x * 2) / 2 : by rwa mul_div_cancel (f x) char_prop
    ... = (1 + 1) / 2 : by rw h2
    ... = 2 / 2 : by refl
    ... = 1 : by rwa div_self, },
  rwa [← sub_eq_zero, ← fn_lem4_1 F f h h0, fn_thm3 F f h X, add_left_eq_self] at h3,
end

lemma fn_lem2_5 (char_ne_2 : ring_char F ≠ 2) : ∀ f : F → F, fn_eq F f → f 0 = 1 → injective f :=
begin
  intros f h h0 x y h1,
  rw ← sub_eq_zero,
  apply fn_lem2_4 F char_ne_2 f h h0,
  exact fn_lem2_3 F f h h0 x y h1,
end

theorem fn_thm2 (char_ne_2 : ring_char F ≠ 2) : ∀ f : F → F, fn_eq F f → f 0 = 1 → f = 1 - id :=
begin
  intros f h h0,
  apply fn_thm4 F f h h0,
  exact fn_lem2_5 F char_ne_2 f h h0,
end



---- Wrap up for char F ≠ 2
theorem A6_sol_char_neq_2 (char_ne_2 : ring_char F ≠ 2) :
  ∀ f : F → F, fn_eq F f ↔ (f = 0 ∨ f = 1 - id ∨ f = id - 1) :=
begin
  intros f,
  symmetry; split,
  { intros h,
    rcases h with h | h | h,
    all_goals {
      subst h,
      intros x y,
      simp; ring,
    }, },
  { intros h,
    by_cases h0 : f = 0,
    { left,
      exact h0, },
    { right,
      have h1 := fn_lem3_3 F f h h0,
      rw sq_eq_one_iff at h1,
      cases h1 with h1 h1,
      { left,
        exact fn_thm2 F char_ne_2 f h h1, },
      { right,
        have h2 := fn_thm1 F f h,
        have h3 : (-f) 0 = 1,
        { simp,
          rw [h1, neg_neg], },
        have h4 := fn_thm2 F char_ne_2 (-f) h2 h3,
        rw [← neg_sub, ← h4, neg_neg], }, }, },
end