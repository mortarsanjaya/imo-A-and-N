import algebra.order.field tactic.linarith

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

variables {R : Type*} [linear_ordered_comm_ring R]

def fn_ineq (f : R → R) := ∀ x y : R, f (x + y) ≤ y * f x + f (f x)



variables {f : R → R} (fineq : fn_ineq f)
include fineq

private lemma lem1 (x : R) : x * f x ≤ 0 :=
begin
  revert x; suffices : ∀ t x : R, f t ≤ (t - x) * f x + f (f x),
    intros x; linarith [this (f (2 * f x)) x, this (f x) (2 * f x)],
  intros t x,
  replace fineq := fineq x (t - x),
  rwa add_sub_cancel'_right at fineq
end

private lemma lem2 (x : R) : f x ≤ 0 :=
begin
  have h := fineq x 0,
  rw [add_zero, zero_mul, zero_add] at h,
  rw ← not_lt; intros h0,
  refine lt_irrefl 0 (lt_of_lt_of_le h0 (le_trans h _)),
  exact nonpos_of_mul_nonpos_right (lem1 fineq (f x)) h0
end



/-- Final solution -/
theorem final_solution (x : R) (h : x ≤ 0) : f x = 0 :=
begin
  have h0 : ∀ y : R, y < 0 → f y = 0 :=
    λ y h, le_antisymm (lem2 fineq y) (nonneg_of_mul_nonpos_right (lem1 fineq y) h),
  rw le_iff_lt_or_eq at h,
  rcases h with h | rfl,
  exact h0 x h,
  cases exists_lt (0 : R) with x h,
  have h1 := fineq x 0,
  rw [add_zero, h0 x h, mul_zero, zero_add] at h1,
  exact le_antisymm (lem2 fineq 0) h1
end

end IMO2011A6
end IMOSL
