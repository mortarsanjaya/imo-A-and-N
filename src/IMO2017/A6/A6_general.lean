import algebra.algebra.basic algebra.char_p.two tactic.field_simp tactic.ring

/-! # IMO 2017 A6 (P2), Generalized Version -/

open function
open_locale classical

namespace IMOSL
namespace IMO2017A6

variables {F : Type*} [field F]

def fn_eq (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y)



section results

variables {f : F → F} (feq : fn_eq f)
include feq

private lemma feq_neg : fn_eq (-f) :=
begin
  intros x y,
  simp only [pi.neg_apply],
  rw [neg_mul_neg, ← neg_add, feq],
end

private lemma fn_lem1_1 {x : F} (x_ne_0 : x ≠ 0) : f (f (x + 1) * f (x⁻¹ + 1)) = 0 :=
begin
  have h := feq (x + 1) (1 + x⁻¹),
  rwa [mul_one_add, add_one_mul, mul_inv_cancel x_ne_0, add_left_eq_self, add_comm _ x⁻¹] at h
end

private lemma fn_lem1_2 (f_ne_0 : f ≠ 0) {c : F} (h : f c = 0) : c = 1 :=
begin
  contrapose f_ne_0,
  rw not_not; funext x,
  rw ← sub_eq_zero at f_ne_0,
  have h0 := fn_lem1_1 feq f_ne_0,
  rw [sub_add_cancel, h, zero_mul] at h0,
  have h1 := feq x 0,
  rwa [mul_zero, add_zero, h0, mul_zero, h0, zero_add] at h1
end

private lemma fn_lem1_3 (f_ne_0 : f ≠ 0) : f 0 ^ 2 = 1 :=
begin
  have h := feq 0 0,
  rw [add_zero, mul_zero, add_left_eq_self, ← sq] at h,
  exact fn_lem1_2 feq f_ne_0 h
end

private lemma fn_lem1_4 (f_ne_0 : f ≠ 0) : f 1 = 0 :=
begin
  have h := feq 0 0,
  rwa [add_zero, mul_zero, add_left_eq_self, ← sq, fn_lem1_3 feq f_ne_0] at h
end



/- From now on, assume that f(0) = 1. One can show that f(0)^2 = 1 and thus f(0) = ±1. -/
variable f0_eq_1 : f 0 = 1
include f0_eq_1

private lemma fn_lem2_0 : f ≠ 0 :=
begin
  contrapose f0_eq_1,
  rw not_not at f0_eq_1,
  rw [f0_eq_1, pi.zero_apply],
  exact zero_ne_one
end

private lemma fn_lem2_1 (f_inj : injective f) : f = λ x, 1 - x :=
begin
  have h : ∀ x : F, f (f x) + f x = 1 :=
    λ x, by have h := feq x 0; rwa [mul_zero, f0_eq_1, mul_one, add_zero] at h,
  funext x,
  rw [← h x, eq_sub_iff_add_eq, add_comm, add_left_inj],
  apply f_inj,
  rw [← add_left_inj (f (f x)), h, add_comm, h]
end

private lemma fn_lem2_2 (x : F) : f (x + 1) + 1 = f x :=
begin
  have h := feq x 1,
  rwa [fn_lem1_4 feq (fn_lem2_0 feq f0_eq_1), mul_zero, mul_one, f0_eq_1, add_comm] at h
end

private lemma fn_lem2_3 (x : F) : f x = 0 ↔ x = 1 :=
begin
  have h := fn_lem2_0 feq f0_eq_1,
  split,
  exact fn_lem1_2 feq h,
  rintros rfl; exact fn_lem1_4 feq h
end



/- Case 1 : char(F) ≠ 2 -/
section case_char_ne_2

private lemma fn_lem3_1 (x : F) : f (f x * (1 + 1)) + (f x + 1) = f (-x) :=
  by rw [← mul_neg_one, ← feq x (-1), ← fn_lem2_2 feq f0_eq_1 (-1 : F), neg_add_self,
         f0_eq_1, ← fn_lem2_2 feq f0_eq_1 (x + -1), neg_add_cancel_right]

private lemma fn_lem3_2 (char_ne_2 : ring_char F ≠ 2) {x : F} (h : f x = f (-x)) : x = 0 :=
begin
  have h0 := fn_lem3_1 feq f0_eq_1 x,
  rwa [← h, ← add_left_comm, add_right_eq_self, ← sub_add_cancel (_ * _) (1 : F),
      fn_lem2_2 feq f0_eq_1, fn_lem2_3 feq f0_eq_1, sub_eq_iff_eq_add,
      mul_left_eq_self₀, ← fn_lem2_2 feq f0_eq_1, add_left_eq_self,
      fn_lem2_3 feq f0_eq_1, add_left_eq_self, or_iff_left] at h0,
  exact ring.two_ne_zero char_ne_2
end

private lemma fn_lem3_3 (char_ne_2 : ring_char F ≠ 2) : injective f :=
begin
  intros x y h,
  have h0 : f (-x) = f (-y) := by rw [← fn_lem3_1 feq f0_eq_1, h, fn_lem3_1 feq f0_eq_1],
  have h1 := feq x (-y),
  rw [h, ← h0, mul_neg, ← neg_mul, mul_comm, ← feq (-x) y, add_right_inj] at h1,
  rw ← add_neg_eq_zero; apply fn_lem3_2 feq f0_eq_1 char_ne_2,
  rw [neg_add, neg_neg, h1]
end

end case_char_ne_2



/- Case 2: char(F) = 2. -/
section case_char_eq_2

variable [char_p F 2]

private lemma fn_lem4_1 (x : F) : f (x + 1) = f x + 1 :=
  by rw [← sub_eq_iff_eq_add, char_two.sub_eq_add, fn_lem2_2 feq f0_eq_1]

private lemma fn_lem4_2 (x : F) : f (x⁻¹ + 1) = (f (x + 1))⁻¹ :=
begin
  rcases eq_or_ne x 0 with rfl | h,
  rw [inv_zero, zero_add, fn_lem1_4 feq (fn_lem2_0 feq f0_eq_1), inv_zero],
  rw [← mul_eq_one_iff_eq_inv₀, mul_comm],
  exact fn_lem1_2 feq (fn_lem2_0 feq f0_eq_1) (fn_lem1_1 feq h),
  contrapose! h,
  rwa [fn_lem2_3 feq f0_eq_1, add_left_eq_self] at h
end

private lemma fn_lem4_3 (a b : F) (h : f (a + 1) * f (b + 1) = 1) :
  f (a + b + 1) = f (a + b + a * b) :=
begin
  have h0 := feq (a + 1) (b + 1),
  rwa [h, fn_lem1_4 feq (fn_lem2_0 feq f0_eq_1), zero_add, add_add_add_comm, add_one_mul,
       mul_add_one, ← add_assoc, ← add_assoc, fn_lem4_1 feq f0_eq_1 (_ + a + b),
       fn_lem4_1 feq f0_eq_1, add_left_inj, add_assoc (a * b), add_comm (a * b)] at h0
end

private lemma fn_lem4_4 (a b : F) (h : f (a + 1) * f (b + 1) = 1) : a * b = 1 :=
begin
  have X : ∀ a b c d : F, f a = f b → f c = f d → a * c = b * d → f (a + c) = f (b + d) :=
  begin
    intros a b c d h0 h1 h2,
    have h3 := feq a c, 
    rwa [h0, h1, h2, ← feq b d, add_right_inj] at h3
  end,

  have f_ne_0 := fn_lem2_0 feq f0_eq_1,
  have h0 : a ≠ 0 :=
    by rintros rfl; rw [zero_add, fn_lem1_4 feq f_ne_0, zero_mul] at h; exact zero_ne_one h,
  have h1 : b ≠ 0 :=
    by rintros rfl; rw [zero_add, fn_lem1_4 feq f_ne_0, mul_zero] at h; exact zero_ne_one h,
  have h2 : (a + b + 1) * (a⁻¹ + b⁻¹ + 1) = (a + b + a * b) * (a⁻¹ + b⁻¹ + a⁻¹ * b⁻¹) :=
    by field_simp [h0, h1]; ring,
  replace h2 := X _ _ _ _ (fn_lem4_3 feq f0_eq_1 a b h) (fn_lem4_3 feq f0_eq_1 _ _
    (by rw [fn_lem4_2 feq f0_eq_1, fn_lem4_2 feq f0_eq_1, ← mul_inv, h, inv_one])) h2,
  clear X,
  let x := a + b⁻¹ + 1,
  let y := b + a⁻¹ + 1,
  have h3 : x + y = (a + b + 1) + (a⁻¹ + b⁻¹ + 1) := by dsimp only [x, y]; ring,
  have h4 : x * y + 1 = (a + b + a * b) + (a⁻¹ + b⁻¹ + a⁻¹ * b⁻¹) :=
    by dsimp only [x, y]; rw ← sub_eq_zero; ring_nf; field_simp [h0, h1],
  rw [← h3, ← h4, fn_lem4_1 feq f0_eq_1] at h2; clear h3 h4,
  have h3 := feq x y,
  rw [h2, add_comm _ (1 : F), ← add_assoc, add_left_eq_self, ← fn_lem4_1 feq f0_eq_1,
      fn_lem2_3 feq f0_eq_1, add_left_eq_self, mul_eq_zero] at h3,
  dsimp only [x, y] at h3,
  cases h3 with h3 h3,
  all_goals {
    rwa [fn_lem2_3 feq f0_eq_1, add_left_eq_self, ← char_two.sub_eq_add, sub_eq_zero] at h3 },
  rwa mul_eq_one_iff_eq_inv₀ h1,
  rwa [mul_comm, mul_eq_one_iff_eq_inv₀ h0]
end

private lemma fn_lem4_5 : injective f :=
begin
  suffices : ∀ a b : F, f (a + 1) = f(b + 1) → a = b,
  { intros a b h,
    apply this,
    rw [fn_lem4_1 feq f0_eq_1, h, fn_lem4_1 feq f0_eq_1] },
  intros a b h,
  rcases eq_or_ne b 0 with rfl | h0,
  rwa [zero_add, fn_lem1_4 feq (fn_lem2_0 feq f0_eq_1), fn_lem2_3 feq f0_eq_1, add_left_eq_self] at h,
  rw [← mul_inv_eq_one₀, ← fn_lem4_2 feq f0_eq_1] at h,
  replace h := fn_lem4_4 feq f0_eq_1 _ _ h,
  rwa mul_inv_eq_one₀ h0 at h,
  contrapose! h0,
  rwa [fn_lem2_3 feq f0_eq_1, add_left_eq_self] at h0
end

end case_char_eq_2



private theorem fn_thm5 : f = λ x, 1 - x :=
begin
  apply fn_lem2_1 feq f0_eq_1,
  by_cases h : ring_char F = 2,
  rw ring_char.eq_iff at h,
  exactI fn_lem4_5 feq f0_eq_1,
  exact fn_lem3_3 feq f0_eq_1 h
end

end results



/-- Final solution -/
theorem final_solution_general (f : F → F) :
  fn_eq f ↔ f = 0 ∨ (f = λ x, x - 1) ∨ (f = λ x, 1 - x) :=
begin
  split,
  { intros feq,
    cases eq_or_ne f 0 with h h,
    left; exact h,
    right,
    have h0 := fn_lem1_3 feq h,
    rw sq_eq_one_iff at h0,
    cases h0 with h0 h0,
    right; exact fn_thm5 feq h0,
    left,
    rw [eq_neg_iff_eq_neg, eq_comm, ← pi.neg_apply f 0] at h0,
    have h1 := feq_neg feq,
    replace h1 := fn_thm5 h1 h0,
    rw [eq_comm, eq_neg_iff_eq_neg] at h1,
    rw h1; funext x; simp only [pi.neg_apply, neg_sub, sub_left_inj] },
  { rintros (rfl | h),
    intros x y; simp only [pi.zero_apply, add_zero],
    have h0 : fn_eq (λ x, x - (1 : F)) := by intros x y; simp only []; ring,
    rcases h with rfl | rfl,
    exact h0,
    replace h0 := feq_neg h0,
    conv at h0 { congr, rw pi.neg_def, funext, rw neg_sub },
    exact h0 }
end

end IMO2017A6
end IMOSL
