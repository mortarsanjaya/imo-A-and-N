import
  algebra.algebra.basic
  algebra.char_p.basic
  algebra.char_p.two
  logic.function.basic

/-
  IMO 2017 A6 (P2)
  Determine all functions f : ℝ → ℝ such that, for all x, y ∈ ℝ,
          f(f(x) f(y)) + f(x + y) = f(xy).
          
  See https://www.imo-official.org/problems/IMO2017SL.pdf.
  Solution is actually implemented as part of a more general solution.
  
-/

namespace IMO2017A6





universe u
variable F : Type u
variable [field F]

open function
local attribute classical.prop_decidable



def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)









/-
  1. General results
-/

---- Show that f satisfies the equation iff -f also satisfies the equation
theorem fn_thm1_1 : ∀ f : F → F, fn_eq F f → fn_eq F (-f) :=
begin
  intros f h x y,
  simp,
  rwa [← (h x y), neg_add],
end



---- Show that either f x = 0 → x = 1 or ∀ x, f x = 0
lemma fn_lem1_2_1 : ∀ f : F → F, fn_eq F f → (∃ x : F, x ≠ 1 ∧ f x = 0) → f 0 = 0 :=
begin
  intros f h h0,
  rcases h0 with ⟨c, h0, h1⟩,
  let d := c / (c - 1),
  have h2 := h c d,
  suffices : (c + d = c * d),
  { rwa [this, add_left_eq_self, h1, zero_mul] at h2, },
  calc c + c / (c - 1) = (c * (c - 1) + c) / (c - 1) : _
  ... = (c * (c - 1) + c * 1) / (c - 1) : by rw mul_one
  ... = c * (c - 1 + 1) / (c - 1) : by rw ← mul_add
  ... = c * c / (c - 1) : by rw sub_add_cancel
  ... = c * (c / (c - 1)) : by rw mul_div_assoc,
  { rw add_div_eq_mul_add_div,
    intros h3,
    rw sub_eq_zero at h3,
    contradiction, },
end

lemma fn_lem1_2_2 : ∀ f : F → F, fn_eq F f → f 0 = 0 → f = 0 :=
begin
  intros f h h0,
  apply funext; intros x,
  have h1 := h x 0,
  rwa [h0, mul_zero, mul_zero, add_zero, h0, zero_add] at h1,
end

theorem fn_thm1_2 : ∀ f : F → F, fn_eq F f → (∃ x : F, x ≠ 1 ∧ f x = 0) → f = 0 :=
begin
  intros f h h0,
  apply fn_lem1_2_2 F f h,
  exact fn_lem1_2_1 F f h h0,
end



---- Now assume that f ≠ 0. Show that f x = 0 ↔ x = 1
lemma fn_lem1_3_1 : ∀ f : F → F, fn_eq F f → f (f 0 ^ 2) = 0 :=
begin
  intros f h,
  have h0 := h 0 0,
  rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h0,
end

lemma fn_lem1_3_2 : ∀ f : F → F, fn_eq F f → f ≠ 0 → ∀ x : F, f x = 0 → x = 1 :=
begin
  intros f h h0 x h1,
  by_cases h2 : (x = 1),
  exact h2,
  exfalso; apply h0,
  apply fn_thm1_2 F f h,
  use x; split; assumption,
end

lemma fn_lem1_3_3 : ∀ f : F → F, fn_eq F f → f ≠ 0 → f 0 ^ 2 = 1 :=
begin
  intros f h h0,
  apply fn_lem1_3_2 F f h h0,
  exact fn_lem1_3_1 F f h,
end

lemma fn_lem1_3_4 : ∀ f : F → F, fn_eq F f → f 1 = 0 :=
begin
  intros f h,
  by_cases h0 : f ≠ 0,
  { have h1 := fn_lem1_3_1 F f h,
    rwa fn_lem1_3_3 F f h h0 at h1, },
  { rw not_not at h0,
    rw h0,
    simp, },
end

theorem fn_thm1_3 : ∀ f : F → F, fn_eq F f → f ≠ 0 → ∀ x : F, f x = 0 ↔ x = 1 :=
begin
  intros f h h0 x,
  split,
  { exact fn_lem1_3_2 F f h h0 x, },
  { intros h1,
    subst h1,
    exact fn_lem1_3_4 F f h, },
end



---- If f is injective, we are done; plus some auxiliary lemmas
lemma fn_lem1_4_1 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x : F, f (x + 1) = f x - 1 :=
begin
  intros f h h0 x,
  have h1 := h x 1,
  rw [fn_lem1_3_4 F f h, mul_zero, mul_one, h0] at h1,
  rw [← h1, add_sub_cancel'],
end

lemma fn_lem1_4_2 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x : F, f (f x) + f x = 1 :=
begin
  intros f h h0 x,
  have h1 := h x 0,
  rwa [mul_zero, h0, mul_one, add_zero] at h1,
end

theorem fn_thm1_4 : ∀ f : F → F, fn_eq F f → f 0 = 1 → injective f → f = 1 - id :=
begin
  intros f h h0 h1,
  apply funext; simp,
  intros x,
  have h2 := fn_lem1_4_2 F f h h0 x,
  have h3 := fn_lem1_4_2 F f h h0 (f x),
  rw [add_comm, ← h2, add_right_inj] at h3,
  rwa [← h2, h1 h3, add_sub_cancel'],
end









/-
2.  Solution for the case char(F) ≠ 2
-/

---- Injectivity result and characterization result for char F ≠ 2
lemma fn_lem2_1 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ x : F, f (x - 1) = f x + 1 :=
begin
  intros f h h0 x,
  rw [← sub_eq_iff_eq_add, ← fn_lem1_4_1 F f h h0, sub_add_cancel],
end

lemma fn_lem2_2 : ∀ f : F → F, fn_eq F f → f 0 = 1 → ∀ (x : F), f (f x * 2) + f x + 1 = f (-x) :=
begin
  intros f h h0 x,
  suffices : f (-1) = 2,
  { have h1 := h x (-1),
    rwa [← sub_eq_add_neg, fn_lem2_1 F f h h0, mul_neg_one, ← add_assoc, this] at h1, },
  rw [← sub_left_inj, ← fn_lem1_4_1 F f h h0, neg_add_self, h0],
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
  rw [← add_eq_zero_iff_eq_neg, ← fn_lem2_1 F f h h0, fn_thm1_3 F f h X, sub_eq_iff_eq_add'] at h2,
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
  rwa [← sub_eq_zero, ← fn_lem1_4_1 F f h h0, fn_thm1_3 F f h X, add_left_eq_self] at h3,
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
  apply fn_thm1_4 F f h h0,
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
      have h1 := fn_lem1_3_3 F f h h0,
      rw sq_eq_one_iff at h1,
      cases h1 with h1 h1,
      { left,
        exact fn_thm2 F char_ne_2 f h h1, },
      { right,
        have h2 := fn_thm1_1 F f h,
        have h3 : (-f) 0 = 1,
        { simp,
          rw [h1, neg_neg], },
        have h4 := fn_thm2 F char_ne_2 (-f) h2 h3,
        rw [← neg_sub, ← h4, neg_neg], }, }, },
end









/-
  3. Progress for the case char(F) = 2
-/

---- An alternative definition for the FE on the shifted function f + 1
def fn_eq_s1 (f : F → F) := ∀ x : F, f (x + 1) = f x + 1
def fn_eq_s2 (f : F → F) := ∀ x : F, f x = 0 ↔ x = 0
def fn_eq_s3 (f : F → F) := ∀ x y : F, f (f x * f y) + f(x + y) = f(x * y + x + y)



---- Transfer between the shifted FE and the original FE
lemma fn_lem3_1_1 (char_eq_2 : ring_char F = 2) (f : F → F) (f_ne_0 : f ≠ 0) :
  ∀ f : F → F, fn_eq F f → fn_eq_s1 F (f + 1) :=
begin
  intros f h x,
  simp,
  sorry,
end

lemma fn_lem3_1_2 (char_eq_2 : ring_char F = 2) (f : F → F) (f_ne_0 : f ≠ 0) :
  fn_eq F f → fn_eq_s2 F (f + 1) :=
begin
  sorry,
end

lemma fn_lem3_1_3 (char_eq_2 : ring_char F = 2) (f : F → F) (f_ne_0 : f ≠ 0) :
  fn_eq F f → fn_eq_s3 F (f + 1) :=
begin
  sorry,
end














end IMO2017A6
