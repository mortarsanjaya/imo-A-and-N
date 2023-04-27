import IMO2012.A5.A5_basic
  IMO2012.A5.extra.nnreal_odd_ext
  extra.real_prop.real_quadratic_sol

/-! # IMO 2012 A5, Case 2: `f(-1) = 0` (exclusive on `ℝ`) -/

namespace IMOSL
namespace IMO2012A5

/-- The respective solution for this case. -/
theorem case2_answer {S : Type*} [comm_ring S] [is_domain S] :
  good (λ x : S, x ^ 2 - 1) :=
  λ x y, by rw [sub_sub_sub_cancel_right, sq_sub_sq, add_add_add_comm,
    add_comm 1 y, ← mul_add_one, ← add_one_mul, ← sub_sub_sub_eq, ← mul_sub_one,
    ← sub_one_mul, mul_mul_mul_comm, ← sq_sub_sq, ← sq_sub_sq, one_pow]



variables {S : Type*} [ring S] [is_domain S]
  {f : ℝ → S} (h : good f) (h0 : f 0 = -1) (h1 : f (-1) = 0)
include h h0 h1

/-- The hypothesis `h0 : f(0) = -1` is actually unneeded here. -/
private lemma case2_lem1 (x : ℝ) : f (-x) = f x :=
  by rw [← sub_eq_zero, map_neg_sub_map2 h, h1, mul_zero]

private lemma case2_lem2 (x : ℝ) : f (|x|) = f x :=
  (abs_choice x).elim (congr_arg f) (λ h2, (congr_arg f h2).trans $ case2_lem1 h h0 h1 x)

private lemma case2_lem3 (x y : ℝ) : f (x * y + 1) - f (x * y - 1) = f (x + y) - f (x - y) :=
  by rw [sub_eq_sub_iff_sub_eq_sub, h, ← case2_lem1 h h0 h1 y, ← h, ← sub_eq_add_neg,
    mul_neg, ← neg_sub 1 (x * y), add_comm, ← sub_eq_add_neg, case2_lem1 h h0 h1]

private lemma case2_lem4 (a b : ℝ) :
  f ((a ^ 2 - b ^ 2) / (2 * 2) + 1) - f ((a ^ 2 - b ^ 2) / (2 * 2) - 1) = f a - f b :=
  by rw [sq_sub_sq, ← div_mul_div_comm, case2_lem3 h h0 h1, ← add_div,
    add_add_sub_cancel, half_add_self, ← sub_div, add_sub_sub_cancel, half_add_self]

private lemma case2_lem5 {a b c d : ℝ} (h2 : a ^ 2 - b ^ 2 = c ^ 2 - d ^ 2) :
  f a - f b = f c - f d :=
  by rw [← case2_lem4 h h0 h1, h2, case2_lem4 h h0 h1]


open nnreal
open_locale nnreal

private lemma case2_lem6 (u v : ℝ≥0) : f (sqrt (u + v)) = f (sqrt u) + f (sqrt v) + 1 :=
begin
  rw [← add_neg_eq_iff_eq_add, ← h0, ← sub_eq_sub_iff_add_eq_add],
  apply case2_lem5 h h0 h1,
  iterate 3 { rw [real.coe_sqrt, real.sq_sqrt (coe_nonneg _)] },
  rw [sq, zero_mul, sub_zero, sub_eq_iff_eq_add, nonneg.coe_add]
end

private lemma case2_lem7 (u v : ℝ≥0) : f (u + v) = f u + f v + f (sqrt (2 * u * v)) + 2 :=
  by rw [← nonneg.coe_add, ← sqrt_sq (u + v), add_sq', case2_lem6 h h0 h1,
    case2_lem6 h h0 h1, sqrt_sq, sqrt_sq, add_right_comm _ 1 (f _), add_assoc, ← bit0]

private lemma case2_lem8 (u v : ℝ≥0) : f (u * v) + 1 = (f u + 1) * (f v + 1) :=
  let h2 := case2_lem7 h h0 h1, h3 : f 1 = 0 := (case2_lem1 h h0 h1 1).symm.trans h1 in
  by have h4 := h u v; rw [← nonneg.coe_one, ← nonneg.coe_mul, h2, nonneg.coe_one,
        h3, add_zero, mul_one, h2, add_sub_add_right_eq_sub, mul_assoc,
        add_sub_add_right_eq_sub, nonneg.coe_mul, sub_eq_iff_eq_add, ← add_assoc] at h4;
    rw [h4, add_one_mul, mul_add_one, ← add_assoc]

private lemma case2_lem9 : ∃ φ : ℝ≥0 →+* S, f = λ x : ℝ, φ (x.nnabs ^ 2) - 1 :=
  ⟨⟨λ x, f (sqrt x) + 1,
      by rw [sqrt_one, nonneg.coe_one, ← case2_lem1 h h0 h1, h1, zero_add],
      λ x y, by rw [sqrt_mul, nonneg.coe_mul, case2_lem8 h h0 h1],
      by rw [sqrt_zero, nonneg.coe_zero, h0, neg_add_self],
      λ x y, by rw [add_add_add_comm, ← add_assoc, ← case2_lem6 h h0 h1]⟩,
    funext (λ x, by rw [ring_hom.coe_mk, add_sub_cancel,
      nnreal.sqrt_sq, real.coe_nnabs, case2_lem2 h h0 h1])⟩

theorem case2_sol : ∃ φ : ℝ →+* S, f = λ x, φ x ^ 2 - 1 :=
begin
  rcases case2_lem9 h h0 h1 with ⟨φ, rfl⟩,
  refine ⟨(φ : ℝ →+* S), funext (λ x, _)⟩,
  rw [map_pow, extra.nnreal_ring_hom.coe_map_sq]
end

end IMO2012A5
end IMOSL
