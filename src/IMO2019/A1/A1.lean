import data.int.basic data.pi.algebra data.int.order.basic algebra.ring.regular

/-! # IMO 2019 A1 (P1) -/

namespace IMOSL
namespace IMO2019A1

open function

/-- Final solution -/
theorem final_solution {N : ℤ} (h : N ≠ 0) (f : ℤ → ℤ) :
  (∀ a b : ℤ, f (N * a) + N * f b = f (f (a + b))) ↔
    f = 0 ∨ ∃ c : ℤ, f = λ n, N * n + c :=
begin
  ---- Easier direction: `←`
  symmetry; refine ⟨λ h0 a b, _, λ h0, _⟩,
  rcases h0 with rfl | ⟨c, rfl⟩,
  rw [pi.zero_apply, zero_add, pi.zero_apply, mul_zero, pi.zero_apply],
  rw [add_right_comm, ← mul_add, ← add_assoc, ← mul_add],

  ---- Harder direction: `→`; start with proving linearity
  have h1 : ∀ n : ℤ, N * (f (n + 1) - f n) = f N - f 0 :=
    λ n, by rw [mul_sub, ← mul_zero N, sub_eq_sub_iff_add_eq_add,
      add_comm, h0, zero_add, add_comm, ← h0, mul_one],
  replace h1 : ∀ n : ℤ, f (n + 1) - f n = f 1 - f 0 :=
    λ n, int.eq_of_mul_eq_mul_left h (by rw [h1, ← h1 0, zero_add]),
  replace h1 : ∃ q c : ℤ, f = λ n, q * n + c :=
  begin
    refine ⟨f 1 - f 0, f 0, funext (λ n, int.induction_on' n 0 _ _ _)⟩,
    rw [mul_zero, zero_add],
    rintros k - h2; rw [mul_add_one, add_right_comm, ← h2, ← h1 k, add_sub_cancel'_right],
    rintros k - h2; rw [mul_sub_one, ← add_sub_right_comm,
      ← h2, ← h1 (k - 1), sub_add_cancel, sub_sub_cancel]
  end,

  ---- Now prove that either `q = N` or `q = c = 0`
  rcases h1 with ⟨q, c, rfl⟩,
  rcases eq_or_ne N q with rfl | h1,
  right; use c,
  left; funext n,
  replace h0 := h0 n 0,
  rwa [add_right_comm, add_zero, add_left_inj, mul_left_comm, ← mul_add,
    ← add_assoc, ← mul_add, add_zero, mul_eq_mul_right_iff, or_iff_right h1] at h0
end

end IMO2019A1
end IMOSL
