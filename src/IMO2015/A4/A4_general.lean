import algebra.algebra.basic algebra.char_p.two dynamics.fixed_points.basic

namespace IMOSL
namespace IMO2015A4

variables {R : Type*} [comm_ring R] [is_domain R]

/--
  IMO 2015 A4 (P5), Generalized Version
  
  Let R be a domain.
  Find all functions f : R → R such that, for all x, y ∈ R,
          f(x + f(x + y)) + f(xy) = x + f(x + y) + y f(x).

  Answer: f = id : x ↦ x and f = x ↦ 2 - x.

  See http://www.imo-official.org/problems/IMO2015SL.pdf.
  The official solution works perfectly only for the case char(R) ≠ 2.
  For the case char(R) = 2, one may obtain f(x²) + 1 = (f(x) + 1)(x + 1) for all x ∈ R.
  This turns out to be enough in proving that f must be the identity.

  In this file, we follow the official solution for the case char(R) ≠ 2.
  We also work with our own solution for the case char(R) = 2.
  
  Solution for the case char(R) = 2:
    Proceed equally in case f(0) ≠ 0.
    From now on, assume that f(0) = 0.
    As in the case char(R) ≠ 2, We also prove that f(-1) = -1 and
    (1)        ∀ x ∈ R, x + f(x + 1) is a fixed point.
    The equality f(1) = 1 is now immediate from f(-1) = -1 since -1 = 1.

    Plugging in x = 0 into the original equation yields
    (2)       ∀ y ∈ R, f(y) is a fixed point.
    Next, plugging y = x + 1 into the original equation yields
    (3)       ∀ x ∈ R, f(x + 1) + f(x² + x) = (x + 1) (f(x) + 1).
    Comparing (3) with x and with x + 1, we will get x f(x + 1) = (x + 1) f(x).
    In particular, if x is a non-zero fixed point, then x + 1 is a fixed point.
    But 1 is a fixed point as well, so we get
    (4).      ∀ x ∈ R, x is a fixed point → x + 1 is a fixed point.
    Next, plugging y = x into the original equation gives us
              ∀ x ∈ R, f(x²) + 1 = (x + 1) (f(x) + 1)
    Then, by (2) and (4),
    (5).      ∀ x ∈ R, (x + 1) (f(x) + 1) is a fixed point.
    Next, by plugging y = 0 into the original equation, we get
    (6).      ∀ x ∈ R, x + f(x) is a fixed point.
    Finally, for any t ∈ R, plug (x, y) ↦ (t + 1, f(t) + 1) into the original equation.
    By (6), x + y = t + f(t) is a fixed point, while by (2) and (4), y is a fixed point.
    Thus the equation simplifies to
              f(xy) = yf(x) → f((t + 1) (f(t) + 1)) = (f(t) + 1) f(t + 1).
    But by (5), (t + 1) (f(t) + 1) is also a fixed point.
    Thus, either f(t) = 1 or t + 1 is a fixed point.
    However, if f(t) = 1, then (6) yields that t + 1 is a fixed point.
    Thus, either way, for any t ∈ R, t + 1 is a fixed point.
    Replacing t with x - 1 gives us f(x) = x for all x ∈ R, as desired.
-/
def fn_eq (f : R → R) := ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x







open function
open_locale classical

namespace results



---- General lemmas
section general

variables {f : R → R} (feq : fn_eq f)
include feq



lemma fn_lem1_1 :
  ∀ x : R, is_fixed_pt f (x + f (x + 1)) :=
begin
  intros x,
  have h := feq x 1,
  rwa [one_mul, mul_one, add_left_inj] at h,
end

lemma fn_lem1_2 :
  f 0 ≠ 0 → ∀ x : R, is_fixed_pt f x → x = 1 :=
begin
  unfold is_fixed_pt; intros h x h0,
  have h1 := feq 0 x,
  rw [zero_add, zero_add, h0, h0, zero_mul, add_right_inj, eq_comm, mul_left_eq_self₀] at h1,
  cases h1 with h1 h1,
  exact h1,
  exfalso; exact h h1,
end

lemma fn_lem1_3 :
  f 0 ≠ 0 → f = 2 - id :=
begin
  intros h; apply funext; intros x,
  rw [pi.sub_apply, id.def, pi.bit0_apply, pi.one_apply],
  have h0 := fn_lem1_2 feq h _ (fn_lem1_1 feq (x - 1)),
  rwa [sub_add_cancel, add_comm, ← eq_sub_iff_add_eq, ← sub_add, add_comm, ← add_sub_assoc] at h0,
end

lemma fn_lem1_4 :
  f 0 = 0 → f (-1) = -1 :=
begin
  intros h,
  have h0 := fn_lem1_1 feq (-1),
  rwa [neg_add_self, h, add_zero] at h0,
end

end general



---- Solution for the case char(R) ≠ 2, assuming f(0) = 0
section case_char_ne_2

variable char_ne_2 : ring_char R ≠ 2
include char_ne_2

variables {f : R → R} (feq : fn_eq f) (h : f 0 = 0)
include feq h



lemma fn_lem2_1 :
  f 1 = 1 :=
begin
  have h0 := feq 1 (-1),
  rw [add_neg_self, h, add_zero, one_mul, fn_lem1_4 feq h, neg_one_mul,
      eq_add_neg_iff_add_eq, add_right_comm, eq_comm, eq_add_neg_iff_add_eq,
      ← two_mul (f 1), ← two_mul, mul_one, eq_comm, mul_right_eq_self₀] at h0,
  cases h0 with h0 h0,
  exact h0,
  exfalso; exact ring.two_ne_zero char_ne_2 h0,
end

lemma fn_lem2_2 :
  ∀ x : R, f (1 + f (x + 1)) + f x = 1 + f (x + 1) + x :=
begin
  intros x,
  have h0 := feq 1 x,
  rwa [add_comm 1 x, one_mul, fn_lem2_1 char_ne_2 feq h, mul_one] at h0,
end

lemma fn_lem2_3 :
  ∀ x : R, is_fixed_pt f x → is_fixed_pt f (x + 1) → is_fixed_pt f (x + 2) :=
begin
  unfold is_fixed_pt; intros x h0 h1,
  have h2 := fn_lem2_2 char_ne_2 feq h x,
  rwa [h1, h0, add_left_inj, add_comm 1 (x + 1), add_assoc] at h2,
end

lemma fn_lem2_4 :
  ∀ x : R, is_fixed_pt f (x + f (x + 1) + 2) :=
begin
  intros x,
  apply fn_lem2_3 char_ne_2 feq h _ (fn_lem1_1 feq x),
  have h0 := feq (x + 1) 0,
  rw [mul_zero, zero_mul, add_zero, add_zero, h, add_zero] at h0,
  rwa add_right_comm,
end

lemma fn_lem2_5 :
  ∀ x : R, f (-x) = - (f x) :=
begin
  intros x,
  have h0 := fn_lem2_4 char_ne_2 feq h (x - (1 + 1)),
  change (2 : R) with (1 + 1 : R) at h0,
  rw [add_assoc, sub_add_add_cancel, sub_add, add_sub_cancel] at h0,
  have h1 := feq x (-1),
  rwa [← sub_eq_add_neg, is_fixed_pt.eq h0, add_right_inj, mul_neg_one, neg_one_mul] at h1,
end

lemma fn_lem2_6 :
  ∀ x : R, - (f (1 + f (x + 1))) + f x = - (1 + f (x + 1)) + x :=
begin
  intros x,
  have h0 := feq (-1) (-x),
  rwa [← neg_add, fn_lem2_5 char_ne_2 feq h, ← neg_add, fn_lem2_5 char_ne_2 feq h,
      fn_lem1_4 feq h, neg_mul_neg, one_mul, neg_mul_neg, mul_one, add_comm 1 x] at h0,
end

theorem fn_thm2 :
  f = id :=
begin
  apply funext; intros x,
  rw ← mul_right_inj' (ring.two_ne_zero char_ne_2),
  calc 2 * f x = f x + f x : by rw two_mul
  ... = f (1 + f (x + 1)) + - (f (1 + f (x + 1))) + (f x + f x) : by rw [add_neg_self, zero_add]
  ... = f (1 + f (x + 1)) + f x + (- (f (1 + f (x + 1))) + f x) : by rw add_add_add_comm
  ... = 1 + f (x + 1) + x + (- (f (1 + f (x + 1))) + f x) : by rw fn_lem2_2 char_ne_2 feq h x
  ... = 1 + f (x + 1) + x + (- (1 + f (x + 1)) + x) : by rw fn_lem2_6 char_ne_2 feq h x
  ... = 1 + f (x + 1) + - (1 + f (x + 1)) + (x + x) : by rw add_add_add_comm
  ... = x + x : by rw [add_neg_self, zero_add]
  ... = 2 * x : by rw ← two_mul,
end

end case_char_ne_2



---- Solution for the case char(R) = 2, assuming f(0) = 0
section case_char_eq_2

variable [char_p R 2]

variables {f : R → R} (feq : fn_eq f) (h : f 0 = 0)
include feq h



lemma fn_lem3_1 :
  f 1 = 1 :=
begin
  rw ← char_two.neg_eq (1 : R),
  exact fn_lem1_4 feq h,
end

lemma fn_lem3_2 :
  ∀ x : R, is_fixed_pt f (f x) :=
begin
  intros x,
  have h0 := feq 0 x,
  rwa [zero_add, zero_add, zero_mul, h, add_zero, mul_zero, add_zero] at h0,
end

lemma fn_lem3_3 :
  ∀ x : R, f (x * (x + 1)) = (x + 1) * (f x + 1) + f (x + 1) :=
begin
  intros x,
  have h0 := feq x (x + 1),
  rwa [← add_assoc, char_two.add_self_eq_zero, zero_add, fn_lem3_1 feq h, add_comm,
      ← eq_sub_iff_add_eq, ← mul_one_add, add_comm 1 (f x), char_two.sub_eq_add] at h0,
end

lemma fn_lem3_4 :
  ∀ x : R, is_fixed_pt f x → is_fixed_pt f (x + 1) :=
begin
  unfold is_fixed_pt; intros x h0,
  by_cases h1 : x + 1 = 0,
  rw [h1, h],
  have h2 := fn_lem3_3 feq h (x + 1),
  rwa [← char_two.sub_eq_add (x + 1), add_sub_cancel, mul_comm, fn_lem3_3 feq h x, h0,
      mul_add_one x, ← char_two.sub_eq_add _ x, add_sub_cancel, ← eq_sub_iff_add_eq,
      char_two.sub_eq_add, ← add_one_mul, mul_right_inj' h1, eq_comm] at h2,
end

lemma fn_lem3_5 :
  ∀ x : R, f (x * x) + 1 = (x + 1) * (f x + 1) :=
begin
  intros x,
  have h0 := feq x x,
  rw [char_two.add_self_eq_zero, h, add_zero, add_comm, ← eq_sub_iff_add_eq] at h0,
  rw [h0, char_two.sub_eq_add, add_assoc, add_comm x, add_one_mul, mul_add_one],
end

lemma fn_lem3_6 :
  ∀ x : R, is_fixed_pt f (x + f x) :=
begin
  intros x,
  have h0 := feq x 0,
  rwa [add_zero, zero_mul, add_zero, mul_zero, h, add_zero] at h0,
end

lemma fn_lem3_7 :
  ∀ x y : R, y ≠ 0 → is_fixed_pt f y → is_fixed_pt f (x + y) → is_fixed_pt f (x * y) →
    is_fixed_pt f x :=
begin
  unfold is_fixed_pt; intros x y h0 h1 h2 h3,
  have h4 := feq x y,
  rwa [h2, ← add_assoc, char_two.add_self_eq_zero, zero_add, h1,
       add_right_inj, h3, mul_comm, mul_right_inj' h0, eq_comm] at h4,
end

theorem fn_thm3 :
  f = id :=
begin
  suffices : ∀ x : R, f (x + 1) = x + 1,
  { apply funext; intros x,
    have h0 := this (x - 1),
    rwa sub_add_cancel at h0 },
  intros x,
  by_cases h0 : f x + 1 = 0,

  ---- First, if f(x) = 1, then x + 1 is indeed a fixed point.
  { rw [← char_two.sub_eq_add, sub_eq_zero] at h0,
    have h1 := fn_lem3_6 feq h x,
    rwa h0 at h1 },

  ---- Now consider the case f(x) ≠ 1.
  { refine fn_lem3_7 feq h (x + 1) (f x + 1) h0 _ _ _,
    exact fn_lem3_4 feq h _ (fn_lem3_2 feq h x),
    rw [add_add_add_comm, char_two.add_self_eq_zero, add_zero],
    exact fn_lem3_6 feq h x,
    rw ← fn_lem3_5 feq h x,
    exact fn_lem3_4 feq h _ (fn_lem3_2 feq h (x * x)) },
end

end case_char_eq_2



end results







/-- Final solution -/
theorem final_solution_general (f : R → R) :
  fn_eq f ↔ f = id ∨ f = 2 - id :=
begin
  split,
  { intros feq,
    by_cases h0 : f 0 = 0,
    left; by_cases h1 : ring_char R = 2,
    have _inst_3 := ring_char.of_eq h1,
    exactI results.fn_thm3 feq h0,
    exact results.fn_thm2 h1 feq h0,
    right; exact results.fn_lem1_3 feq h0 },
  { rintros (rfl | rfl) x y; simp,
    exact mul_comm x y,
    ring }
end

end IMO2015A4
end IMOSL
