import algebra.char_p.two

/-! # IMO 2009 A7, Generalized Version -/

namespace IMOSL
namespace IMO2009A7

open function
open_locale non_zero_divisors

variables {R : Type*} [ring R]

def fn_eq (f : R → R) := ∀ x y : R, f (x * f (x + y)) = f (f x * y) + x ^ 2



section results

section general

variables [is_domain R] {f : R → R} (feq : fn_eq f)
include feq

private lemma lem1_1 : f 0 = 0 :=
begin
  have h := feq 0 (f (f 0)),
  rw [zero_mul, sq, zero_mul, add_zero] at h,
  replace feq := feq (f 0) 0,
  rw [add_zero, ← h, mul_zero, self_eq_add_right] at feq,
  exact pow_eq_zero feq
end

private lemma lem1_2 (x : R) : f (x * f x) = x ^ 2 :=
begin
  have h := feq x 0,
  rwa [add_zero, mul_zero, lem1_1 feq, zero_add] at h
end

private lemma lem1_3 : injective f :=
begin
  have h : ∀ x : R, f x = 0 ↔ x = 0 :=
  begin
    refine λ x, ⟨λ h, _, λ h, by rw [h, lem1_1 feq]⟩,
    have h0 := lem1_2 feq x,
    rw [h, mul_zero, lem1_1 feq, eq_comm] at h0,
    exact pow_eq_zero h0
  end,
  intros x y h0,
  have h1 := feq x (y - x),
  rw [add_sub_cancel'_right, ← h0, lem1_2 feq, self_eq_add_left, h, mul_eq_zero] at h1,
  cases h1 with h1 h1,
  rw [(h x).mp h1, eq_comm, ← h, ← h0, h1],
  rw [eq_comm, ← sub_eq_zero, h1]
end

private lemma lem1_4 (x : R) : f (-x) = -f x :=
begin
  have h := lem1_2 feq (-x),
  rw [neg_sq, ← lem1_2 feq, neg_mul] at h,
  replace h := lem1_3 feq h,
  rw [← add_eq_zero_iff_neg_eq, ← mul_add, mul_eq_zero] at h,
  cases h with h h,
  rw [h, neg_zero, lem1_1 feq, neg_zero],
  rw [← add_eq_zero_iff_eq_neg, h]
end

private lemma lem1_5 : f 1 ^ 2 = 1 :=
begin
  have h := lem1_2 feq 1,
  rw [one_mul, one_pow] at h,
  replace feq := lem1_2 feq (f 1),
  rwa [h, mul_one, h, eq_comm] at feq
end

private lemma lem1_6 (h : f 1 = 1) (x : R) : f (f (x + 1)) = f x + 1 :=
begin
  replace feq := feq 1 x,
  rwa [one_mul, h, one_mul, one_pow, add_comm] at feq
end

end general



section case_char_ne_2

variables [is_domain R] {f : R → R} (feq : fn_eq f)
include feq

private lemma lem2_1 (h : f 1 = 1) (x : R) : f (x + 2) = f x + 2 :=
begin
  rw [bit0, ← add_assoc, ← add_assoc, ← lem1_6 feq h],
  generalize : x + 1 = y,
  have fodd := lem1_4 feq,
  have h0 := feq (-1) (y + 1),
  rwa [neg_one_sq, fodd, h, neg_one_mul, fodd, add_comm, add_neg_cancel_right,
       neg_one_mul, fodd, ← sub_eq_iff_eq_add, ← neg_add', neg_inj, eq_comm] at h0
end

private lemma lem2_2 (R2ne0 : (2 : R) ≠ 0) (h : f 1 = 1) (x : R) : f x = x :=
begin
  have h0 := lem2_1 feq h,
  have h1 := h0 0,
  rw [lem1_1 feq, zero_add] at h1,
  have h2 := feq 2 x,
  rw [add_comm, h0, mul_add, mul_two, ← add_assoc, h0,
      h0, add_assoc, ← two_mul, sq, add_left_inj, h1] at h2,
  replace h2 := lem1_3 feq h2,
  rwa [mul_eq_mul_left_iff, or_iff_left R2ne0] at h2,
end

private lemma lem2_3 (R2ne0 : (2 : R) ≠ 0) : f = id ∨ f = has_neg.neg :=
begin
  have h := lem1_5 feq,
  rw sq_eq_one_iff at h,
  cases h with h h,
  left; funext x; exact lem2_2 feq R2ne0 h x,
  right; suffices : fn_eq (-f),
  { funext x,
    rw [eq_neg_iff_eq_neg, eq_comm],
    refine lem2_2 this R2ne0 _ x,
    rw [pi.neg_apply, h, neg_neg] },
  intros x y,
  replace h := lem1_4 feq,
  simp only [pi.neg_apply],
  rw [mul_neg, neg_mul, h, feq, neg_neg, h, neg_neg]
end

end case_char_ne_2



section case_char_eq_2

variables [is_domain R] [char_p R 2] {f : R → R} (feq : fn_eq f)
include feq

private lemma lem3_1 : f 1 = 1 :=
begin
  have h := lem1_5 feq,
  rwa [sq_eq_one_iff, char_two.neg_eq, or_self] at h
end

private lemma lem3_2 {c d : R} (h : f c = d + 1) (h0 : f d = c + 1) : c = d ∨ c = d + 1 :=
begin
  have f1eq1 := lem3_1 feq,
  have cdcomm : (c + 1) * (d + 1) = (d + 1) * (c + 1) :=
  begin
    rw [← h, add_one_mul, mul_add_one, add_left_inj],
    apply lem1_3 feq,
    have h1 := feq c c,
    rw [char_two.add_self_eq_zero, lem1_1 feq, mul_zero, lem1_1 feq,
        eq_comm, add_eq_zero_iff_eq_neg, char_two.neg_eq] at h1,
    rw [h1, lem1_2 feq]
  end,
  have h1 := feq c (c + 1),
  have h2 := feq d (d + 1),
  rw [← add_assoc, char_two.add_self_eq_zero, zero_add, f1eq1, mul_one] at h1 h2,
  rw [h, ← cdcomm, ← sub_eq_iff_eq_add, char_two.sub_eq_add, add_right_comm] at h1,
  rw [h0, ← h1, add_right_comm, add_left_inj, add_assoc, ← sub_eq_iff_eq_add'] at h2,
  rw [add_one_mul, mul_add_one, add_one_mul, mul_add_one, ← add_assoc, ← add_assoc,
      add_left_inj, add_right_comm, add_left_inj, add_left_inj] at cdcomm,
  replace h1 : (c + d) * (c + d) = c ^ 2 + d ^ 2 := by rw [sq, sq, add_mul, mul_add, add_assoc,
    add_right_inj, mul_add, ← add_assoc, cdcomm, char_two.add_self_eq_zero, zero_add],
  rwa [char_two.sub_eq_add, ← h1, eq_comm, ← sub_eq_zero, ← mul_sub_one, mul_eq_zero, sub_eq_zero,
      add_eq_zero_iff_eq_neg, add_comm, ← eq_neg_add_iff_add_eq, char_two.neg_eq] at h2
end

private lemma lem3_3 : f = id :=
begin
  funext x,
  have h := lem1_6 feq (lem3_1 feq) (x + 1),
  rw [add_assoc, char_two.add_self_eq_zero, add_zero] at h,
  cases lem3_2 feq (lem1_6 feq (lem3_1 feq) x) h with h0 h0,
  { replace h0 := lem1_3 feq h0,
    rw add_right_eq_self at h0,
    exfalso; exact one_ne_zero h0 },
  { rw [h0, add_assoc, char_two.add_self_eq_zero, add_zero] at h,
    exact lem1_3 feq h }
end

end case_char_eq_2

end results



/-- Final solution -/
theorem final_solution [is_domain R] (f : R → R) : fn_eq f ↔ f = id ∨ f = has_neg.neg :=
begin
  split,
  { intros feq,
    cases ne_or_eq (ring_char R) 2 with h h,
    exact lem2_3 feq (ring.two_ne_zero h),
    rw ring_char.eq_iff at h,
    left; exactI lem3_3 feq },
  { rintros (rfl | rfl) x y,
    simp only [id.def]; rw [mul_add, add_comm, sq],
    rw [mul_neg, neg_neg, neg_mul, neg_neg, mul_add, add_comm, sq] }
end

end IMO2009A7
end IMOSL
