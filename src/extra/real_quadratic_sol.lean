import data.real.sqrt

/-!
# Roots of quadratic equations over ℝ
-/

open real

namespace IMOSL
namespace extra

lemma exists_add_eq_mul_eq {x y : ℝ} (h : 4 * y ≤ x ^ 2) : ∃ u v : ℝ, u + v = x ∧ u * v = y :=
begin
  use [(x + sqrt (x ^ 2 - 4 * y)) / 2, (x - sqrt (x ^ 2 - 4 * y)) / 2]; split,
  rw [← add_div, add_add_sub_cancel, ← mul_two, mul_div_cancel x two_ne_zero],
  rw [div_mul_div_comm, ← sq_sub_sq, sq_sqrt, sub_sub_cancel, bit0, ← two_mul, mul_div_cancel_left],
  apply mul_ne_zero; exact two_ne_zero,
  rwa sub_nonneg
end

lemma add_mul_root_quadr {u v x y : ℝ} (h : u + v = x) (h0 : u * v = y) : u ^ 2 - x * u + y = 0 :=
  by rw [← h, ← h0, sq, ← sub_mul, sub_add_cancel', mul_comm, mul_neg, neg_add_self]

lemma exists_root_quadr {x y : ℝ} (h : 4 * y ≤ x ^ 2) : ∃ t : ℝ, t ^ 2 + x * t + y = 0 :=
begin
  rcases exists_add_eq_mul_eq h with ⟨u, v, h0, h1⟩,
  use -u; rw [neg_sq, mul_neg, ← sub_eq_add_neg],
  exact add_mul_root_quadr h0 h1
end

end extra
end IMOSL
