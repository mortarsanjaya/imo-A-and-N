import
  IMO2017.A6.A6_general
  algebra.char_p.basic
  algebra.char_p.two
  data.set.basic

/-
  Solution of 2017 A6 for the case char(F) ≠ 2
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]







namespace case_char_ne_2

open function
variable char_ne_2 : ring_char F ≠ 2
include char_ne_2
variable f : F → F



---- Injectivity result for char F ≠ 2
lemma fn_lem1 (feq : fn_eq F f) :
  f 0 = 1 → ∀ x : F, f (x - 1) = f x + 1 :=
begin
  intros h x,
  rw [← sub_eq_iff_eq_add, ← general.fn_lem4_1 F f feq h, sub_add_cancel],
end

lemma fn_lem2 (feq : fn_eq F f) :
  f 0 = 1 → ∀ (x : F), f (f x * 2) + f x + 1 = f (-x) :=
begin
  intros h x,
  suffices : f (-1) = 2,
  { have h0 := feq x (-1),
    rwa [← sub_eq_add_neg, fn_lem1 F char_ne_2 f feq h,
         mul_neg_one, ← add_assoc, this] at h0, },
  rw [← sub_left_inj, ← general.fn_lem4_1 F f feq h, neg_add_self, h],
  norm_num,
end

lemma fn_lem3 (feq : fn_eq F f) :
  f 0 = 1 → ∀ x y : F, f x = f y → f (x - y) = f (-(x - y)) :=
begin
  intros h x y h0,
  have h1 : f (-x) = f (-y) :=
    by rw [← fn_lem2 F char_ne_2 f feq h, ← fn_lem2 F char_ne_2 f feq h, h0],
  have h2 := feq x (-y),
  rw [mul_neg, ← neg_mul, ← feq (-x) y, h0, h1, mul_comm, add_right_inj] at h2,
  rwa [sub_eq_add_neg, neg_add, neg_neg],
end

lemma fn_lem4 (feq : fn_eq F f) :
  f 0 = 1 → ∀ x : F, f x = f (-x) → x = 0 :=
begin
  intros h x h0,
  have X : f ≠ 0,
  { intros h1; subst h1,
    simp at h,
    exact h, },
  have h1 := fn_lem2 F char_ne_2 f feq h x,
  rw [← h0, add_assoc, ← eq_sub_iff_add_eq, sub_add_cancel'] at h1,
  rw [← add_eq_zero_iff_eq_neg, ← fn_lem1 F char_ne_2 f feq h,
      general.fn_thm3 F f feq X, sub_eq_iff_eq_add'] at h1,
  have char_prop : 2 ≠ (0 : F),
  { intros h2,
    have h3 : (-1 : F) = 1,
    { calc (-1 : F) = 0 - 1 : by rw zero_sub
      ... = 2 - 1 : by rw ← h2
      ... = 1 : by norm_num, },
    rw neg_one_eq_one_iff at h3,
    contradiction, },
  have h2 : f x = 1,
  { calc f x = (f x * 2) / 2 : by rwa mul_div_cancel (f x) char_prop
    ... = (1 + 1) / 2 : by rw h1
    ... = 2 / 2 : by refl
    ... = 1 : by rwa div_self, },
  rwa [← sub_eq_zero, ← general.fn_lem4_1 F f feq h,
       general.fn_thm3 F f feq X, add_left_eq_self] at h2,
end

lemma fn_lem5 (feq : fn_eq F f) :
  f 0 = 1 → injective f :=
begin
  intros h x y h0,
  rw ← sub_eq_zero,
  apply fn_lem4 F char_ne_2 f feq h,
  exact fn_lem3 F char_ne_2 f feq h x y h0,
end

theorem fn_thm2 (feq : fn_eq F f) :
  f 0 = 1 → f = 1 - id :=
begin
  intros h,
  apply general.fn_thm4 F f feq h,
  exact fn_lem5 F char_ne_2 f feq h,
end



---- Wrapper
theorem fn_all :
  set_of (fn_eq F) = {0, 1 - id, id - 1} :=
begin
  rw set.ext_iff; simp,
  intros f,
  split,
  { intros h,
    by_cases h0 : f = 0,
    { left; exact h0, },
    { right,
      have h1 := general.fn_lem3_3 F f h h0,
      rw sq_eq_one_iff at h1,
      cases h1 with h1 h1,
      { left; exact fn_thm2 F char_ne_2 f h h1, },
      { right,
        have h2 := general.fn_thm1 F f h,
        have h3 : (-f) 0 = 1 := by simp; rw [h1, neg_neg],
        have h4 := fn_thm2 F char_ne_2 (-f) h2 h3,
        rw [← neg_sub, ← h4, neg_neg], }, }, },
  { intros h,
    rcases h with h | h | h; subst h,
    { intros _ _; simp, },
    { intros _ _; simp; ring, },
    { intros _ _; simp; ring, }, },
end

end case_char_ne_2







end IMO2017A6
