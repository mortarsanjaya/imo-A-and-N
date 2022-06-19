import
  algebra.algebra.basic
  algebra.char_p.basic
  algebra.char_p.two
  dynamics.fixed_points.basic
  data.set.basic
  tactic.observe

namespace IMO2015A4

universe u
variable {R : Type u}
variable [comm_ring R]
variable [is_domain R]

/--
  IMO 2015 A4 (P5), Generalized Version
  
  Let R be a domain.
  Find all functions f : R → R such that, for all x, y ∈ R,
          f(x + f(x + y)) + f(xy) = x + f(x + y) + yf(x).

  Answer: f = x ↦ 2 - x and f = id : x ↦ x.

  See http://www.imo-official.org/problems/IMO2015SL.pdf.
  The official solution works perfectly only for the case char(R) ≠ 2.
  For the case char(R) = 2, one may obtain f(x²) + 1 = (f(x) + 1)(x + 1) for all x ∈ R.
  This turns out to be enough in proving that f must be the identity.

  This file will follow the whole official solution for the case char(R) ≠ 2.
  We will also work with our own solution for the case char(R) = 2 in this file.
  

-/
def fn_eq (f : R → R) :=
  ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + y * f x



open function
open_locale classical







---- General lemmas
section general

variable {f : R → R}
variable feq : fn_eq f
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
  intros h x h0,
  have h1 := feq 0 x,
  rw [zero_add, zero_add, is_fixed_pt.eq h0, is_fixed_pt.eq h0,
      zero_mul, add_right_inj, eq_comm, mul_left_eq_self₀] at h1,
  cases h1 with h1 h1,
  exact h1,
  contradiction,
end

lemma fn_lem1_3 :
  f 0 ≠ 0 → f = 2 - id :=
begin
  intros h; apply funext; intros x,
  rw [pi.sub_apply, id.def, pi.bit0_apply, pi.one_apply],
  have h0 := fn_lem1_2 feq h _ (fn_lem1_1 feq (x - 1)),
  rwa [sub_add_cancel, add_comm, ← eq_sub_iff_add_eq,
       ← sub_add, add_comm, ← add_sub_assoc] at h0,
end

lemma fn_lem1_4 :
  f 0 = 0 → f (-1) = -1 :=
begin
  intros h,
  have h0 := fn_lem1_1 feq (-1),
  rwa [neg_add_self, h, add_zero] at h0,
end



end general



---- Specific solution for the case char(R) ≠ 2
---- We will assume f(0) = 0 as the case f(0) ≠ 0 is solved.
section case_char_ne_2

variable char_ne_2 : ring_char R ≠ 2
include char_ne_2

lemma two_ne_zero_R :
  (2 : R) ≠ 0 :=
begin
  intros h,
  apply char_ne_2,
  apply char_p.ring_char_of_prime_eq_zero,
  exact nat.prime_two,
  rw [nat.cast_bit0, nat.cast_one, h],
end

variable {f : R → R}
variable feq : fn_eq f
variable h : f 0 = 0
include feq h



lemma fn_lem2_1 :
  f 1 = 1 :=
begin
  have h0 := feq 1 (-1),
  rw [add_neg_self, h, add_zero, one_mul, fn_lem1_4 feq h, ← sub_eq_zero] at h0,
  ring_nf at h0,
  rw [sub_eq_zero, mul_right_eq_self₀] at h0,
  cases h0 with h0 h0,
  exact h0,
  exfalso; exact two_ne_zero_R char_ne_2 h0,
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
  apply fn_lem2_3 char_ne_2 feq h,
  exact fn_lem1_1 feq x,
  have h0 := feq (x + 1) 0,
  rw [mul_zero, zero_mul, add_zero, add_zero, h, add_zero] at h0,
  rwa add_right_comm,
end

lemma fn_lem2_5 :
  ∀ x : R, f (-x) = - (f x) :=
begin
  intros x,
  have h0 := fn_lem2_4 char_ne_2 feq h (x - 2),
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
  rw ← mul_right_inj' (two_ne_zero_R char_ne_2),
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



section case_char_eq_2

variable [char_p R 2]

variable {f : R → R}
variable feq : fn_eq f
variable h : f 0 = 0
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



---- Wrapper
theorem IMO2015A4_sol_general :
  set_of fn_eq = ({id, 2 - id} : set (R → R)) :=
begin
  rw set.ext_iff; intros f,
  rw [set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff]; split,
  { intros h,
    by_cases h0 : f 0 = 0,
    left; by_cases h1 : ring_char R = 2,
    exact @fn_thm3 R _inst_1 _inst_2 (ring_char.of_eq h1) f h h0,
    exact fn_thm2 h1 h h0,
    right; exact fn_lem1_3 h h0 },
  { intros h,
    cases h with h h; rw h; intros x y,
    rw [id.def, id.def, id.def, id.def, mul_comm],
    simp only [pi.bit0_apply, id.def, pi.one_apply, pi.sub_apply]; ring },
end







end IMO2015A4
