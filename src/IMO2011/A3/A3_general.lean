import
  algebra.ring.basic 
  algebra.group_power.basic
  tactic.ring
namespace IMO2011A3

universe u
variable {R : Type u}
variables [comm_ring R] [is_domain R] [nontrivial R]

/--
  IMO 2011 A3, Generalized Version

  Let R be a non-trivial domain such that 2 has an inverse in R.
  Determine all pairs of (f, g) functions R → R such that, for all x, y ∈ R,
          g(f(x + y)) = f(x) + (2x + y) g(y).

  Answer: (f, g) = (0, 0) and (f, g) = (x ↦ x² + C, id) for some C ∈ R.

  See https://www.imo-official.org/problems/IMO2011SL.pdf.
  We will follow the official Solution.
  It adopts directly to any domain R with 2 having a double-sided inverse.

  Note:
  1. We will only put the condition of 2 having an inverse when necessary.
  2. The non-triviality is actually not required, but the trivial ring case is trivial.
  3. It seems that even the case char(R) = 2 is too ugly to even consider.
-/
def fn_eq (f g : R → R) :=
  ∀ x y : R, g (f (x + y)) = f x + (2 * x + y) * g y







open function

namespace results



---- Extra lemmas needed to solve the problem
section extra

lemma ravi_subst (exists_inv_2 : ∃ t : R, 2 * t = 1) (x y z : R) :
  ∃ a b c : R, x = b + c ∧ y = c + a ∧ z = a + b :=
begin
  cases exists_inv_2 with t h,
  use [(y + z - x) * t, (z + x - y) * t, (x + y - z) * t],
  repeat { split }; ring_nf; rw [h, one_mul],
end

lemma poly_deg_2_zero (two_ne_0 : (2 : R) ≠ 0)
    {A B C : R} (h : ∀ x : R, A * x ^ 2 + B * x + C = 0) :
  A = 0 ∧ B = 0 ∧ C = 0 :=
begin
  have h0 : (A * 1 ^ 2 + B * 1 + C) - (A * (-1) ^ 2 + B * (-1) + C) = 0 :=
    by rw [h, h, sub_zero],
  rw [one_pow, neg_one_sq, mul_one, add_sub_add_right_eq_sub,
      add_sub_add_left_eq_sub, ← mul_sub, sub_neg_eq_add, mul_comm, mul_eq_zero] at h0,
  cases h0,
  contradiction,
  have h1 := h 0,
  rw [sq, mul_zero, mul_zero, zero_add, mul_zero, zero_add] at h1,
  have h2 := h 1,
  rw [h0, zero_mul, add_zero, h1, add_zero, one_pow, mul_one] at h2,
  repeat { split }; assumption,
end

end extra



---- All functions satisying fn_eq are described here
section answer

theorem fn_ans1 :
  fn_eq (0 : R → R) 0 :=
begin
  intros x y,
  rw [pi.zero_apply, pi.zero_apply, pi.zero_apply, mul_zero, add_zero],
end

theorem fn_ans2 (C : R) :
  fn_eq ((λ x : R, x ^ 2) + const R C) (id : R → R) :=
begin
  intros x y,
  simp only [id.def, pi.add_apply, const_apply],
  rw [add_right_comm, add_left_inj, add_mul, add_sq, ← sq, add_assoc],
end

end answer



---- We prove that there are no other functions satisfying fn_eq here
section solution

variables {f g : R → R} (feq : fn_eq f g)
include feq

lemma fn_lem1 :
  ∀ x : R, g (f x) = f (-x) :=
begin
  intros x,
  have h := feq (-x) (2 * x),
  rwa [mul_neg, neg_add_self, zero_mul, add_zero, two_mul, neg_add_cancel_left] at h,
end

lemma fn_lem2 :
  ∀ a b : R, f (-a) - f (-b) = (a - b) * g (a + b) :=
begin
  intros a b,
  have h := feq (-b) (b + a),
  rwa [two_mul, add_assoc, neg_add_cancel_left, fn_lem1 feq, add_comm,
      ← sub_eq_iff_eq_add, add_comm, ← sub_eq_add_neg, add_comm] at h,
end

lemma fn_lem3 (exists_inv_2 : ∃ t : R, 2 * t = 1) :
  ∀ x y z : R, (y - x) * g z + (z - y) * g x + (x - z) * g y = 0 :=
begin
  intros x y z,
  rcases ravi_subst exists_inv_2 x y z with ⟨a, b, c, h, h0, h1⟩,
  have h2 : ∀ u v w : R, u + v - (w + u) = v - w :=
    by intros; rw [add_comm w u, ← sub_sub, add_sub_right_comm, sub_self, zero_add],
  rw [h, h0, h1, h2, h2, h2, ← fn_lem2 feq, ← fn_lem2 feq, ← fn_lem2 feq,
      sub_add_sub_cancel, sub_add_sub_cancel, sub_self],
end

lemma fn_lem4 (exists_inv_2 : ∃ t : R, 2 * t = 1) :
  ∃ A B : R, ∀ x : R, g x = A * x + B :=
begin
  use [g 1 - g 0, g 0]; intros x,
  have h := fn_lem3 feq exists_inv_2 0 x 1,
  rwa [zero_sub, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero, sub_zero,
      one_sub_mul, ← add_comm_sub, ← mul_sub, mul_comm, eq_comm] at h,
end

lemma fn_lem5 {A B : R} (h : ∀ x : R, g x = A * x + B) :
  ∀ x : R, f x = A * x ^ 2 - B * x + f 0 :=
begin
  intros x,
  have h0 := fn_lem2 feq (-x) 0,
  rwa [sub_zero, add_zero, neg_zero, neg_neg, sub_eq_iff_eq_add, h, mul_add, mul_comm,
       mul_assoc, ← sq, neg_sq, mul_comm (-x), mul_neg, ← sub_eq_add_neg] at h0,
end

lemma fn_lem6 {A B : R} (h : ∀ x : R, g x = A * x + B) :
  ∀ x : R, (A ^ 2 - A) * x ^ 2 + -(A + 1) * B * x + (A * f 0 + B - f 0) = 0 :=
begin
  intros x,
  have h0 := fn_lem1 feq x,
  rw [h, fn_lem5 feq h x, fn_lem5 feq h (-x), ← sub_eq_zero] at h0,
  nth_rewrite 2 ← h0; ring,
end

lemma fn_lem7 (two_ne_0 : (2 : R) ≠ 0) {A B : R} (h : ∀ x : R, g x = A * x + B) :
  B = 0 ∧ (A = 1 ∨ (A = 0 ∧ f 0 = 0)) :=
begin
  rcases poly_deg_2_zero two_ne_0 (fn_lem6 feq h) with ⟨h0, h1, h2⟩,
  rw [sq, ← sub_one_mul, mul_eq_zero, sub_eq_zero] at h0,
  cases h0 with h0 h0,

  -- A = 1
  { split,
    rwa [h0, one_mul, add_comm, add_sub_cancel] at h2,
    left; exact h0 },
  
  -- A = 0
  { rw [h0, zero_add, neg_one_mul, neg_eq_zero] at h1,
    split,
    exact h1,
    right; split,
    exact h0,
    rwa [h0, zero_mul, zero_add, h1, zero_sub, neg_eq_zero] at h2 },
end

theorem fn_sol (exists_inv_2 : ∃ t : R, 2 * t = 1) :
  (f, g) = (0, 0) ∨ ∃ C : R, (f, g) = ((λ x : R, x ^ 2) + const R C, id) :=
begin
  rcases fn_lem4 feq exists_inv_2 with ⟨A, B, h⟩,
  have two_ne_0 : (2 : R) ≠ 0,
  { intros h0,
    cases exists_inv_2 with t X,
    rw [h0, zero_mul, eq_comm] at X,
    exact one_ne_zero X },
  have h3 := fn_lem5 feq h,
  rcases fn_lem7 feq two_ne_0 h with ⟨h0, h1 | ⟨h1, h2⟩⟩,

  ---- Case 1: A = 1
  { right; use f 0,
    rw [prod.mk.inj_iff]; split,
    rw funext_iff; intros x,
    rw [h3, h0, zero_mul, sub_zero, h1, one_mul, pi.add_apply, const_apply],
    rw funext_iff; intros x,
    rw [h, h0, add_zero, h1, one_mul, id.def] },

  ---- Case 2: A = 0 and f 0 = 0
  { left; rw [prod.mk.inj_iff]; split,
    rw funext_iff; intros x,
    rw [h3, h2, add_zero, h0, zero_mul, sub_zero, h1, zero_mul, pi.zero_apply],
    rw funext_iff; intros x,
    rw [h, h0, add_zero, h1, zero_mul, pi.zero_apply] },
end

end solution



end results







theorem final_solution_general (exists_inv_2 : ∃ t : R, 2 * t = 1) :
  set_of (λ s : (R → R) × (R → R), fn_eq s.fst s.snd) =
    {(0, 0)} ∪ (λ C : R, ((λ x : R, x ^ 2) + const R C, id)) '' set.univ :=
begin
  rw set.ext_iff; intros f,
  rw [set.mem_set_of_eq, set.singleton_union, set.mem_insert_iff,
      set.image_univ, set.range, set.mem_set_of_eq]; split,

  ---- All functions satisfying fn_eq are in the RHS set
  { intros feq,
    rcases results.fn_sol feq exists_inv_2 with h | ⟨C, h⟩,
    left; rw [← h, prod.mk.eta],
    right; use C; rw [← h, prod.mk.eta] },
  
  ---- All functions on the RHS satisfy fn_eq
  { intros h,
    rcases h with h | ⟨C, h⟩,
    rw h; exact results.fn_ans1,
    rw ← h; exact results.fn_ans2 C },
end

end IMO2011A3
