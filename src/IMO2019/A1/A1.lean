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
  simp_rw [pi.zero_apply, zero_add, mul_zero],
  simp only []; rw [add_right_comm, ← mul_add, ← add_assoc, ← mul_add],

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
  dsimp only [] at h0,
  rcases eq_or_ne q N with rfl | h1,
  right; use c,
  have h2 := h0 0 0,
  rw [mul_zero, add_zero, mul_zero, zero_add, add_comm, add_left_inj,
      mul_eq_mul_right_iff, eq_comm, or_iff_right h1] at h2,
  subst h2; replace h0 := h0 1 0,
  simp_rw [mul_zero, add_zero, mul_one] at h0,
  rw [mul_zero, add_zero, mul_eq_mul_left_iff, eq_comm, or_iff_right h1] at h0,
  left; simp_rw [h0, zero_mul, add_zero]; refl
end

end IMO2019A1
end IMOSL
