import algebra.order.field tactic.linarith

/-! # IMO 2011 A6 (P3) -/

namespace IMOSL
namespace IMO2011A6

variables {F : Type*} [linear_ordered_field F]

def fn_ineq (f : F → F) := ∀ x y : F, f (x + y) ≤ y * f x + f (f x)



section results

variables {f : F → F} (fineq : fn_ineq f)
include fineq

private lemma fn_lem1 (t x : F) : f t ≤ t * f x - x * f x + f (f x) :=
begin
  replace fineq := fineq x (t - x),
  rwa [add_sub_cancel'_right, sub_mul] at fineq
end

private lemma fn_lem2 (x : F) (h : x < 0) : 0 ≤ f x :=
begin
  have h0 : x * f x ≤ 0 :=
    by linarith [(fn_lem1 fineq (f (2 * f x)) x), (fn_lem1 fineq (f x) (2 * f x))],
  rwa [← div_le_iff_of_neg' h, zero_div] at h0
end

private lemma fn_lem3 (x : F) : f x ≤ 0 :=
begin
  rw ← not_lt; intros h,
  let M := x - f (f x) / f x,
  have h0 : ∀ t : F, t < M → f t < 0,
  { intros t h0,
    apply lt_of_le_of_lt (fn_lem1 fineq t x),
    rwa [← sub_mul, ← lt_neg_iff_add_neg, ← lt_div_iff h,
         sub_lt_iff_lt_add', neg_div, ← sub_eq_add_neg] },
  cases exists_lt (min M 0) with C h1,
  rw lt_min_iff at h1,
  cases h1 with h1 h2,
  exact not_lt_of_le (fn_lem2 fineq C h2) (h0 C h1)
end

end results



/-- Final solution -/
theorem final_solution {f : F → F} (fineq : fn_ineq f) (x : F) (h : x ≤ 0) : f x = 0 :=
begin
  apply le_antisymm (fn_lem3 fineq x),
  rw le_iff_lt_or_eq at h,
  rcases h with h | rfl,
  exact fn_lem2 fineq x h,
  cases exists_lt (0 : F) with x h,
  replace h := le_antisymm (fn_lem2 fineq x h) (fn_lem3 fineq x),
  have h0 := fineq x 0,
  rwa [zero_mul, zero_add, add_zero, ← h] at h0
end

end IMO2011A6
end IMOSL
