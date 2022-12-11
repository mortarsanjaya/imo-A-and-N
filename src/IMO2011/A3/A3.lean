import algebra.ring.basic ring_theory.non_zero_divisors tactic.apply_fun

/-! # IMO 2011 A3, Generalized Version -/

namespace IMOSL
namespace IMO2011A3

open function
open_locale non_zero_divisors

def good {R : Type*} [ring R] (f g : R → R) := ∀ x y : R, g (f (x + y)) = f x + (2 * x + y) * g y



/-- Final solution -/
theorem final_solution {R : Type*} [comm_ring R] (h : (2 : R) ∈ R⁰) {f g : R → R} :
  good f g ↔ ∃ a c : R, (a * (a - 1) = 0 ∧ c * (a - 1) = 0) ∧
    (f = λ x, a * x ^ 2 + c) ∧ g = λ x, a * x :=
begin
  symmetry; simp_rw [mul_sub_one, sub_eq_zero],
  refine ⟨λ h0 x y, _, λ h0, _⟩,

  ---- `←` direction
  { rcases h0 with ⟨a, c, ⟨h0, h1⟩, rfl, rfl⟩,
    simp only []; rw [mul_add, ← mul_assoc, h0, mul_comm a c, h1, add_right_comm,
      add_left_inj, mul_left_comm, ← mul_add, add_mul, ← sq, ← add_assoc, ← add_sq] },
  
  ---- `→` direction
  { -- First, obtain the polynomial identity for `f` and `g`.
    have h1 : ∀ x y : R, (f x - x * g x) - (f y - y * g y) = 2 * (y * g x - x * g y) :=
      λ x y, by rw [mul_sub, sub_eq_sub_iff_add_eq_add, ← add_sub_assoc, add_comm _ (f y),
        ← add_sub_right_comm, sub_eq_sub_iff_add_eq_add, ← mul_assoc, add_assoc,
        ← add_mul, ← h0, ← mul_assoc, add_assoc, ← add_mul, ← h0, add_comm],
    obtain ⟨a, b, rfl⟩ : ∃ a b : R, g = λ x, a * x + b :=
    begin
      refine ⟨g 1 - g 0, g 0, funext (λ x, _)⟩,
      have h2 := congr_arg2 has_add.add (h1 0 x) (h1 x 1),
      simp_rw [sub_add_sub_cancel, h1, zero_mul, one_mul, sub_zero] at h2,
      rwa [← mul_add, mul_cancel_left_mem_non_zero_divisor h, add_sub_left_comm, ← neg_sub,
        ← sub_eq_add_neg, ← mul_sub, eq_sub_iff_add_eq, eq_comm, add_comm, mul_comm] at h2
    end,

    replace h1 : ∃ c : R, f = λ x, a * x ^ 2 - b * x + c :=
    begin
      refine ⟨f 0, funext (λ x, _)⟩,
      replace h1 := h1 x 0,
      simp_rw [zero_mul, mul_zero, zero_add, sub_zero, zero_sub, sub_sub, sub_eq_iff_eq_add] at h1,
      rw [h1, ← add_assoc, add_left_inj, mul_add, add_left_comm, two_mul,
        neg_add_cancel_comm, sub_eq_add_neg, mul_left_comm, sq, mul_comm b]
    end,
    rcases h1 with ⟨c, rfl⟩,

    ---- Now solve for the relations between `a`, `b`, and `c`.
    refine ⟨a, c, _⟩,
    replace h0 := λ x, h0 x (-(2 * x)),
    simp_rw [add_neg_self, zero_mul, add_zero, two_mul, neg_add, add_neg_cancel_left,
      neg_sq, mul_neg, sub_neg_eq_add, mul_add a _ c, add_assoc] at h0,
    have h1 := h0 0; simp only [sq, mul_zero, sub_zero, zero_add] at h1,
    simp_rw [h1, add_left_inj, mul_add, ← mul_assoc] at h0,
    have h2 := h0 1; simp_rw [one_pow, mul_one] at h2,
    replace h0 := h0 (-1); simp_rw [neg_sq, one_pow, mul_neg_one, mul_one] at h0,
    replace h0 := congr_arg2 has_add.add h2 h0,
    rw [sub_neg_eq_add, sub_add_add_cancel, ← sub_eq_add_neg, add_add_sub_cancel,
        ← two_mul, ← two_mul, mul_cancel_left_mem_non_zero_divisor h] at h0,
    suffices : b = 0,
    { subst this; rw add_zero at h1,
      simp_rw [mul_comm c, add_zero, zero_mul, sub_zero],
      exact ⟨⟨h0, h1⟩, rfl, rfl⟩ },
    rw [h0, eq_sub_iff_add_eq, add_assoc, add_right_eq_self] at h2,
    apply_fun has_mul.mul a at h1,
    rw [mul_add, ← mul_assoc, h0, add_right_eq_self] at h1,
    rwa [h1, zero_add] at h2 }
end



/-- Final solution when R is an integral domain -/
theorem final_solution_domain {R : Type*} [comm_ring R] [is_domain R] (h : (2 : R) ∈ R⁰)
  {f g : R → R} : good f g ↔ (f = 0 ∧ g = 0) ∨ ((∃ c : R, f = λ x, x ^ 2 + c) ∧ g = λ x, x) :=
begin
  simp_rw [final_solution h, mul_eq_zero, sub_eq_zero, ← and_or_distrib_right],
  refine ⟨λ h0, _, λ h0, _⟩,
  { rcases h0 with ⟨a, c, ⟨rfl, rfl⟩ | rfl, rfl, rfl⟩,
    left; simp_rw [zero_mul, add_zero],
    exact ⟨rfl, funext zero_mul⟩,
    right; exact ⟨⟨c, by simp_rw one_mul⟩, funext one_mul⟩ },
  { rcases h0 with ⟨rfl, rfl⟩ | ⟨⟨c, rfl⟩, rfl⟩,
    refine ⟨0, 0, or.inl ⟨rfl, rfl⟩, _, funext (λ x, (zero_mul x).symm)⟩,
    simp_rw [zero_mul, add_zero, pi.zero_def],
    exact ⟨1, c, or.inr rfl, by simp_rw one_mul, funext (λ x, (one_mul x).symm)⟩ }
end

end IMO2011A3
end IMOSL
