import algebra.order.field.basic extra.fin4

/-! # IMO 2008 A7 -/

namespace IMOSL
namespace IMO2008A7

lemma step_eq {F : Type*} [field F] {a b c d : F} (h : a + c + b ≠ 0) (h0 : a + c + d ≠ 0) :
  2 * ((a - b) / (a + c + b) - (c - d) / (a + c + d)) =
    (a - c) / (a + c + b) + (a - c) / (a + c + d) +
      3 * (a + c) * (d - b) / ((a + c + b) * (a + c + d)) :=
begin
  rw [← add_sub_add_left_eq_sub d b (a + c), mul_div_assoc, ← inv_sub_inv h h0,
      mul_sub (3 * (a + c)), sub_eq_add_neg (_ * _), ← div_eq_mul_inv,
      ← div_eq_mul_inv, add_add_add_comm, ← add_div, ← sub_eq_add_neg,
      ← sub_div, ← add_sub_add_right_eq_sub _ _ (1 : F), mul_sub, sub_eq_add_neg],
  refine congr_arg2 has_add.add _ _,
  { rw [div_add_one h, ← mul_div_assoc]; refine congr_arg2 has_div.div _ rfl,
    rw [sub_add_add_cancel, bit1, add_one_mul, ← add_assoc (a - c),
        add_right_comm, sub_add_add_cancel, mul_add, two_mul] },
  { rw [div_add_one h0, ← mul_div_assoc, ← neg_div]; refine congr_arg2 has_div.div _ rfl,
    rw [sub_add_add_cancel, neg_eq_iff_eq_neg, neg_sub, bit1, add_one_mul,
        add_comm, mul_add, add_sub_assoc, add_sub_sub_cancel, ← two_mul] }
end



variables {F : Type*} [linear_ordered_field F]

lemma eq_of_abs_sub_sq_eq_zero {a b : F} (h : |a - b| ^ 2 = 0) : a = b :=
  eq_of_abs_sub_eq_zero $ sq_eq_zero_iff.mp h

lemma two_mul_add_pos {a b : F} (h : 0 < a) (h0 : 0 < b) : 0 < 2 * a + b :=
  add_pos (mul_pos two_pos h) h0

lemma div_add_mul_add_le_inv {a b c : F} (h : 0 < a + (b + c))
  (h0 : 0 < (a + b) * (a + c)) (h1 : 0 ≤ b * c) :
  a / ((a + b) * (a + c)) ≤ (a + (b + c))⁻¹ :=
  by rwa [div_le_iff h0, inv_mul_eq_div, le_div_iff h, mul_add,
    mul_add, mul_add, add_mul, add_mul, mul_comm b, add_assoc,
    add_le_add_iff_left, add_le_add_iff_left, le_add_iff_nonneg_right]

lemma abs_sub_le_of_nonneg_le {a b : F} (h : 0 ≤ a) (h0 : 0 ≤ b)
  {c : F} (h1 : a ≤ c) (h2 : b ≤ c) : |a - b| ≤ c :=
  abs_sub_le_iff.mpr ⟨(sub_le_self a h0).trans h1, (sub_le_self b h).trans h2⟩

lemma cauchy_schwarz2 {x y : F} (h : 0 < x) (h0 : 0 < y) (a b : F) :
  (a + b) ^ 2 / (x + y) ≤ a ^ 2 / x + b ^ 2 / y :=
begin
  rw [div_le_iff (add_pos h h0), add_mul, mul_add, div_mul_cancel _ (ne_of_gt h),
      mul_add, div_mul_cancel _ (ne_of_gt h0), add_sq, ← add_assoc, add_le_add_iff_right,
      add_assoc, add_le_add_iff_left, ← mul_div_right_comm, ← mul_div_right_comm,
      div_add_div _ _ (ne_of_gt h) (ne_of_gt h0), le_div_iff (mul_pos h h0),
      mul_assoc 2 a, mul_assoc 2 (a * b), mul_comm x, mul_mul_mul_comm, mul_assoc (a ^ 2),
      ← sq, ← mul_pow,  mul_left_comm x, ← sq, ← mul_pow, ← mul_assoc],
  exact two_mul_le_add_sq (a * y) (b * x)
end

lemma cauchy_schwarz2' {x y : F} (h : 0 < x) (h0 : 0 < y) :
  4 / (x + y) ≤ x⁻¹ + y⁻¹ :=
begin
  rw [bit0, ← two_mul, ← sq, bit0],
  refine (cauchy_schwarz2 h h0 1 1).trans_eq _,
  rw one_pow; exact congr_arg2 has_add.add (one_div x) (one_div y)
end

lemma step_ineq {a b c d : F} (h : 0 < a + c + b) (h0 : 0 < a + c + d) :
  4 * (a - c) ^ 2 / (2 * (a + c) + (b + d))
    + 3 * (a + c) * (a - c) * (d - b) / ((a + c + b) * (a + c + d))
  ≤ 2 * ((a - b) * (a - c) / (a + b + c) + (c - d) * (c - a) / (c + d + a)) :=
begin
  rw [add_right_comm a b, add_comm (c + d), ← add_assoc a, ← neg_sub a c, mul_neg,
      neg_div, ← sub_eq_add_neg, mul_div_right_comm (a - b), mul_div_right_comm (c - d),
      ← sub_mul, ← mul_assoc, step_eq (ne_of_gt h) (ne_of_gt h0), add_mul _ _ (a - c),
      ← mul_div_right_comm, mul_right_comm, add_le_add_iff_right, div_eq_mul_inv (a - c),
      div_eq_mul_inv (a - c), ← mul_add, mul_right_comm, ← sq, mul_comm, mul_div_assoc],
  refine mul_le_mul_of_nonneg_left _ (sq_nonneg _),
  rw [two_mul, add_add_add_comm],
  exact cauchy_schwarz2' h h0
end





/- ### Start of the problem -/

open extra extra.fin4

def target_value (x : fin4 → F) : F :=
  2 * ((x i1 - x i2) * (x i1 - x i3) / (x i1 + x i2 + x i3)
    + (x i2 - x i3) * (x i2 - x i4) / (x i2 + x i3 + x i4)
    + (x i3 - x i4) * (x i3 - x i1) / (x i3 + x i4 + x i1)
    + (x i4 - x i1) * (x i4 - x i2) / (x i4 + x i1 + x i2))

variables {x : fin4 → F} (h : ∀ i : fin4, 0 < x i)
include h

lemma fin4_add3_pos (i j k : fin4) : 0 < x i + x j + x k :=
  add_pos (add_pos (h i) (h j)) (h k)

lemma main_ineq_sharp :
  (4 * (|x i1 - x i3| ^ 2 + |x i2 - x i4| ^ 2) - |x i1 - x i3| * |x i2 - x i4|)
    / (3 * ((x i1 + x i3) + (x i2 + x i4))) ≤ target_value x :=
begin
  ---- Some manipulation, then use the step-inequality
  rw [target_value, add_assoc (_ / _ + _ / _), add_add_add_comm (_ / _), mul_add (2 : F)],
  refine (add_le_add (step_ineq (fin4_add3_pos h i1 i3 i2) (fin4_add3_pos h i1 i3 i4))
    (step_ineq (fin4_add3_pos h i2 i4 i3) (fin4_add3_pos h i2 i4 i1))).trans' _,

  ---- Rewrite and use notation-hiding
  rw [← neg_sub (x i2) (x i4), add_comm (x i3) (x i1)],
  have h0 : 0 < x i1 + x i3 := add_pos (h i1) (h i3),
  have h1 : 0 < x i2 + x i4 := add_pos (h i2) (h i4),
  generalize : x i1 - x i3 = ε,
  generalize : x i2 - x i4 = δ,
  generalize_hyp h2 : x i1 + x i3 = y at h0 ⊢,
  generalize_hyp h3 : x i2 + x i4 = z at h1 ⊢,

  ---- Bash again
  rw [← sq_abs ε, ← sq_abs δ, add_add_add_comm, mul_div_assoc 4 (|ε| ^ 2),
      mul_div_assoc 4 (|δ| ^ 2), ← mul_add, mul_neg, neg_div, ← sub_eq_neg_add,
      ← neg_sub (_ / _), ← sub_eq_add_neg, mul_right_comm _ δ ε, mul_assoc,
      mul_assoc (3 * z), mul_div_right_comm, mul_div_right_comm (3 * z), ← sub_mul],
  refine (sub_le_sub (mul_le_mul_of_nonneg_left (cauchy_schwarz2 (two_mul_add_pos h0 h1)
    (two_mul_add_pos h1 h0) _ _) zero_le_four) (le_abs_self $ _ * (ε * δ))).trans' _,
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le', abs_mul, add_add_add_comm,
      ← mul_add, add_comm z y, ← add_one_mul, ← bit1, ← mul_div_assoc, ← sub_div,
      add_sq', mul_add (4 : F), add_sub_sub_cancel, mul_assoc, ← mul_assoc,
      ← add_one_mul, ← abs_mul ε δ, mul_div_right_comm _ (|ε * δ|)],
  refine mul_le_mul_of_nonneg_right _ (abs_nonneg _),

  have h4 : 0 < (3 : F) := three_pos,
  have h5 : (4 * 2 + 1 : F) / 3 = 3 := by rw [div_eq_iff (ne_of_gt h4), bit0, add_mul,
    bit1, add_one_mul, mul_add_one, add_assoc, add_assoc, ← add_assoc (2 : F), ← two_mul],
  rw [← div_div (4 * 2 + 1 : F), h5, mul_div_assoc, mul_div_assoc, ← mul_sub,
      abs_mul, abs_eq_self.mpr (le_of_lt h4), div_eq_mul_inv (3 : F)],
  refine mul_le_mul_of_nonneg_left _ (le_of_lt h4),
  replace h4 : 0 < (y + x i2) * (y + x i4) := mul_pos (add_pos h0 $ h i2) (add_pos h0 $ h i4),
  replace h5 : 0 < (z + x i3) * (z + x i1) := mul_pos (add_pos h1 $ h i3) (add_pos h1 $ h i1),
  refine abs_sub_le_of_nonneg_le (le_of_lt $ div_pos h0 h4) (le_of_lt $ div_pos h1 h5) _ _,
  rw ← h3; exact div_add_mul_add_le_inv
    (add_pos h0 $ add_pos (h i2) (h i4)) h4 (le_of_lt $ mul_pos (h i2) (h i4)),
  rw [add_comm y, ← h2, add_comm (x i1)]; exact div_add_mul_add_le_inv
    (add_pos h1 $ add_pos (h i3) (h i1)) h5 (le_of_lt $ mul_pos (h i3) (h i1))
end

lemma main_ineq_weak :
  (|x i1 - x i3| ^ 2 + |x i2 - x i4| ^ 2) / ((x i1 + x i3) + (x i2 + x i4))
    ≤ target_value x :=
(main_ineq_sharp h).trans' $ begin
  rw [← div_div, div_le_div_right (add_pos (add_pos (h i1) (h i3)) (add_pos (h i2) (h i4)))],
  have h0 : 0 < (3 : F) := three_pos,
  rw [le_div_iff h0, mul_comm, le_sub_iff_add_le, ← le_sub_iff_add_le', ← sub_mul],
  have h1 : (4 : F) - 3 = 1 := (add_sub_add_left_eq_sub _ _ _).trans (add_sub_cancel _ _),
  rw [h1, one_mul]; refine (two_mul_le_add_sq _ _).trans' _,
  rw [mul_assoc, two_mul, le_add_iff_nonneg_left],
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
end





/- ### Final solution -/

/-- Final solution, inequality -/
theorem final_solution_ineq : 0 ≤ target_value x :=
(main_ineq_weak h).trans' $ div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) $
  le_of_lt $ add_pos (add_pos (h i1) (h i3)) (add_pos (h i2) (h i4))

/-- Final solution, equality case -/
theorem final_solution_eq_case : target_value x = 0 ↔ x i1 = x i3 ∧ x i2 = x i4 :=
⟨λ h0, begin
  have h1 := sq_nonneg (|x i1 - x i3|),
  have h2 := sq_nonneg (|x i2 - x i4|),
  suffices : |x i1 - x i3| ^ 2 + |x i2 - x i4| ^ 2 = 0,
    exact ((add_eq_zero_iff' h1 h2).mp this).imp
      eq_of_abs_sub_sq_eq_zero eq_of_abs_sub_sq_eq_zero,
  refine le_antisymm _ (add_nonneg h1 h2),
  have h4 : 0 < x i1 + x i3 + (x i2 + x i4) :=
    add_pos (add_pos (h i1) (h i3)) (add_pos (h i2) (h i4)),
  have h3 := mul_nonpos_of_nonpos_of_nonneg ((main_ineq_weak h).trans_eq h0) (le_of_lt h4),
  rwa div_mul_cancel _ (ne_of_gt h4) at h3,
end,
λ h0, by rw [target_value, h0.1, h0.2, sub_self, sub_self, mul_zero, mul_zero,
  zero_div, zero_div, add_zero, add_zero, add_zero, mul_zero]⟩

end IMO2008A7
end IMOSL
