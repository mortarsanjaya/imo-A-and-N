import algebra.char_p.two

/-! # IMO 2015 A4 (P5), Generalized Version -/

namespace IMOSL
namespace IMO2015A4

open function

def good {R : Type*} [ring R] (f : R → R) :=
  ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + f x * y



/-- Final solution, case 1: `char(R) ≠ 2` -/
theorem final_solution_char_ne_two {R : Type*} [ring R] [is_domain R] (Rchar : ring_char R ≠ 2) :
  ∀ f : R → R, good f ↔ f = (λ x, x) ∨ f = (λ x, 2 - x) :=
begin
  intros f; symmetry; refine ⟨λ h x y, _, λ h, _⟩,
  rcases h with rfl | rfl; simp only [],
  rw [← add_sub_assoc, ← add_sub_assoc, add_sub_add_left_eq_sub, sub_sub_cancel,
      sub_mul, ← add_sub_assoc, sub_left_inj, two_mul, sub_add_add_cancel, add_comm],
  
  ---- One important equality and the case `f(0) ≠ 0`
  have h0 : ∀ t : R, f (t + f (t + 1)) = t + f (t + 1) :=
    λ t, by replace h := h t 1; rwa [mul_one, mul_one, add_left_inj] at h,
  cases ne_or_eq (f 0) 0 with h1 h1,
  right; funext x,
  replace h := h 0 (x - 1 + f (x - 1 + 1)),
  rwa [zero_add, zero_add, zero_mul, h0, h0, add_right_inj, sub_add_cancel, eq_comm,
       ← sub_eq_zero, ← mul_sub_one, mul_eq_zero, or_iff_right h1, sub_eq_zero,
       ← add_sub_right_comm, sub_eq_iff_eq_add, ← eq_sub_iff_add_eq'] at h,

  ---- The main case, `f(0) = 0`
  ---- First obtain `f(1) = 1` and reduce to `f` being odd
  left; have h2 := h0 (-1),
  rw [neg_add_self, h1, add_zero] at h2,
  replace h2 : f 1 = 1 :=
  begin
    replace h := h 1 (-1),
    rwa [add_neg_self, h1, add_zero, one_mul, h2, mul_neg_one, add_neg_eq_iff_eq_add,
         add_right_comm, eq_add_neg_iff_add_eq, ← two_mul, ← two_mul,
         mul_eq_mul_left_iff, or_iff_left (ring.two_ne_zero Rchar)] at h,
  end,
  suffices h3 : ∀ x : R, f (-x) = -f x,
  { funext x,
    replace h0 := h 1 x,
    rw [one_mul, h2, one_mul] at h0,
    replace h1 := h (-1) (-x),
    rw [← neg_add, h3, ← neg_add, h3, h3, h2, neg_mul_neg, one_mul] at h1,
    generalize_hyp : 1 + f (1 + x) = c at h0 h1,
    replace h0 := congr_arg2 has_add.add h0 h1,
    rwa [add_add_add_comm, add_neg_self, zero_add, add_add_add_comm, add_neg_self, zero_add,
         ← two_mul, ← two_mul, mul_eq_mul_left_iff, or_iff_left (ring.two_ne_zero Rchar)] at h0 },
  
  ---- Now prove that `f` is odd
  intros x,
  rw [← mul_neg_one, ← add_right_inj (f (x + f (x + -1))), h,
      mul_neg_one, add_left_inj, eq_comm, ← sub_eq_add_neg],
  obtain ⟨y, rfl⟩ : ∃ y : R, y + (1 + 1) = x := ⟨x - (1 + 1), sub_add_cancel x _⟩,
  rw [add_sub_assoc, add_sub_cancel, ← bit0, add_right_comm],
  replace h0 := h0 y,
  have h3 := h (y + 1) 0,
  rw [add_zero, mul_zero, mul_zero, add_zero, h1, add_zero, add_right_comm] at h3,
  generalize_hyp : y + f (y + 1) = t at h0 h3 ⊢; clear y,
  replace h := h 1 t,
  rwa [h2, one_mul, h0, add_left_inj, add_comm 1 t, h3, add_left_comm] at h
end



/-- Final solution, case 2: `char(R) = 2` -/
theorem final_solution_char_eq_two {R : Type*} [ring R] [is_domain R] [char_p R 2] :
  ∀ f : R → R, good f ↔ f = (λ x, x) :=
begin
  ---- Easy case and changing `f` to `g + id`
  intros f; symmetry; refine ⟨λ h x y, by subst h, λ h, _⟩,
  unfold good at h,
  obtain ⟨g, rfl⟩ : ∃ g : R → R, g + (λ x, x) = f := ⟨f - id, sub_add_cancel f id⟩,
  rw add_left_eq_self; simp only [pi.add_apply] at h,
  conv at h { find (_ = _) { rw [← add_assoc, add_mul, ← add_assoc _ _ (x * y),
    add_left_inj, add_right_comm _ _ (g (x * y)), add_comm, add_right_inj,
    add_left_comm, ← add_assoc x, char_two.add_self_eq_zero, zero_add] } },
  
  ---- Reduce into two equalities, then obtain `g(0) = 0` and `g(1) = 0`
  suffices : (∀ t : R, g (t + 1) * (t + 1) = g t * t) ∧ ∀ t : R, g (g t * t) = g t,
  { cases this with h0 h1,
    funext t,
    have h2 := h1 t,
    rw [← h0, h1] at h2,
    replace h0 := h0 t,
    rwa [h2, mul_add_one, add_right_eq_self] at h0 },
  have h0 := h 1 1,
  rw [mul_one, mul_one, add_left_eq_self, char_two.add_self_eq_zero] at h0,
  have h1 := h 0 (g 0 + 1),
  rw [zero_mul, zero_add, h0, zero_add, h0, zero_add, mul_add_one, self_eq_add_left, ← sq] at h1,
  replace h1 := pow_eq_zero h1,
  rw [h1, zero_add] at h0,
  refine ⟨λ t, _, λ t, _⟩,

  ---- The first equality
  { replace h : ∀ t : R, g (t + 1) + g (t * (t + 1)) = g t * (t + 1) :=
      λ t, by convert h t (t + 1) using 2;
        rw [← add_assoc t, char_two.add_self_eq_zero, zero_add, h0, zero_add],
    replace h0 := h (t + 1),
    rw [add_assoc, char_two.add_self_eq_zero, add_zero] at h0,
    rw [mul_add_one, ← h0, add_one_mul, ← mul_add_one, add_assoc, add_comm (g (t * _)),
        h, mul_add_one, add_left_comm, char_two.add_self_eq_zero, add_zero] },

  ---- The second equality
  { replace h0 := h t 0,
    rw [add_zero, add_zero, mul_zero, h1, add_zero, mul_zero] at h0,
    have h2 := h 0 t,
    rw [zero_add, zero_mul, h1, zero_mul, add_zero] at h2,
    replace h1 := h (g t) t,
    rw [h2, zero_add, h0, zero_mul, add_eq_zero_iff_eq_neg, char_two.neg_eq] at h1,
    exact h1.symm }
end



/-- Final solution -/
theorem final_solution {R : Type*} [ring R] [is_domain R] :
  ∀ f : R → R, good f ↔ f = (λ x, x) ∨ f = (λ x, 2 - x) :=
begin
  cases ne_or_eq (ring_char R) 2 with h h,
  exact final_solution_char_ne_two h,
  haveI : char_p R 2 := ring_char.of_eq h,
  simp only [char_two.two_eq_zero, char_two.sub_eq_add, zero_add, or_self],
  exact final_solution_char_eq_two
end

end IMO2015A4
end IMOSL
