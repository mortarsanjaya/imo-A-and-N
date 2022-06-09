import
  data.int.basic
  data.nat.basic
  data.set.basic
  tactic.ring

/-
  IMO 2015 A2

  Determine all functions f : ℤ → ℤ such that, for all x, y ∈ ℤ,
          f(x - f(y)) = f(f(x)) - f(y) - 1

  Answer: f = -1 and f = x ↦ x + 1

  See http://www.imo-official.org/problems/IMO2015SL.pdf
  We will follow the official solution.
-/

namespace IMO2015A2

open function

def fn_eq (f : ℤ → ℤ) := ∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1




---- All functions satisying fn_eq are described here
namespace answer

lemma fn_answer1 :
  fn_eq (const ℤ (-1)) :=
begin
  intros _ _; simp,
end

lemma fn_answer2 :
  fn_eq (id + 1) :=
begin
  intros _ _; simp,
  rw [sub_add_eq_add_sub, sub_sub],
end

end answer



---- We prove that there are no other functions satisfying fn_eq here
namespace solution

variable f : ℤ → ℤ
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  f (- f (f 0)) = -1 :=
begin
  have h := feq 0 (f 0),
  rwa [zero_sub, sub_self, zero_sub] at h,
end

lemma fn_lem2 :
  ∀ x : ℤ, f (f x) = f (x + 1) :=
begin
  intros x,
  have h := feq x (-f (f 0)),
  rw [fn_lem1 f feq, sub_neg_eq_add, sub_sub, neg_add_self, sub_zero] at h,
  rw h,
end

lemma fn_lem3 :
  ∀ x y : ℤ, f (x - f y) = f (x + 1) - f y - 1 :=
begin
  intros x y,
  have h := feq x y,
  rwa fn_lem2 f feq at h,
end

lemma fn_lem4 :
  ∀ x : ℤ, f (x - 1 - f x) = -1 :=
begin
  intros x,
  have h := fn_lem3 f feq (x - 1) x,
  rwa [sub_add_cancel, sub_self, zero_sub] at h,
end

lemma fn_lem5 :
  ∀ x : ℤ, f (x + 1) = f x + (f (-1) + 1) :=
begin
  intros x,
  rw [add_comm (f x), ← sub_eq_iff_eq_add],
  calc f (x + 1) - f x = f (x + 1) - f x - 1 + 1 : by rw sub_add_cancel
  ... = f (x - f x) + 1 : by rw ← fn_lem3 f feq
  ... = f (x - f x - 1 + 1) + 1 : by rw sub_add_cancel
  ... = f (f (x - f x - 1)) + 1 : by rw ← fn_lem2 f feq
  ... = f (f (x - 1 - f x)) + 1 : by rw sub_right_comm
  ... = f (-1) + 1 : by rw fn_lem4 f feq,
end

lemma fn_lem6_step1 :
  ∀ (x : ℤ) (n : ℕ), f (x + ↑n) = f x + ↑n * (f (-1) + 1) :=
begin
  intros x n,
  induction n with n; simp,
  rw [← add_assoc, fn_lem5 f feq, n_ih, add_assoc, add_right_inj, add_mul, one_mul],
end

lemma fn_lem6_step2 :
  ∀ (x : ℤ) (n : ℕ), f (x - ↑n) = f x - ↑n * (f (-1) + 1) :=
begin
  intros x n,
  rw [eq_sub_iff_add_eq, ← fn_lem6_step1 f feq, sub_add_cancel],
end

lemma fn_lem6_step3 :
  ∀ x n : ℤ, f (x + n) = f x + n * (f (-1) + 1) :=
begin
  intros x n,
  cases n with n,
  { simp,
    rw fn_lem6_step1 f feq, },
  { have h : -[1+ n] = -↑(n + 1) := by rw int.neg_succ_of_nat_eq; simp,
    rw [h, ← sub_eq_add_neg, fn_lem6_step2 f feq, sub_eq_add_neg, neg_mul],
  }
end

lemma fn_lem6 :
  ∀ x : ℤ, f x = f 0 + x * (f (-1) + 1) :=
begin
  intros x,
  calc f x = f (0 + x) : by rw zero_add
  ... = f 0 + x * (f (-1) + 1) : by rw fn_lem6_step3 f feq,
end

lemma fn_lem7 (a b c d : ℤ) :
  (∀ x : ℤ, a * x + b = c * x + d) → a = c ∧ b = d :=
begin
  intros h,
  have h0 := h 0,
  rw [mul_zero, mul_zero, zero_add, zero_add] at h0,
  have h1 := h 1,
  rw [mul_one, mul_one, h0, add_left_inj] at h1,
  split; assumption,
end

theorem fn_sol :
  f = const ℤ (-1) ∨ f = id + 1 :=
begin
  let A := f (-1) + 1,
  let B := f 0,
  have h : ∀ x : ℤ, f x = A * x + B,
  { intros _,
    rw [fn_lem6 f feq, add_comm, mul_comm], },
  have h0 : ∀ x : ℤ, A * x + (A + B) = A * A * x + (A * B + B),
  { intros x,
    calc A * x + (A + B) = A * (x + 1) + B : by rw [mul_add, mul_one, add_assoc _ A]
    ... = f (x + 1) : by rw ← h
    ... = f (f x) : by rw ← fn_lem2 f feq
    ... = A * A * x + (A * B + B) : by rw [h, h]; ring, },
  have h1 := fn_lem7 f feq _ _ _ _ h0,
  cases h1 with h1 h2,
  rw add_left_inj at h2,
  have h3 : A = 0 ∨ A - 1 = 0 := by rw [← mul_eq_zero, mul_sub, mul_one, sub_eq_zero, ← h1],
  cases h3 with h3 h3,
  { left,
    apply funext,
    intros x; simp,
    rw [h, h3, zero_mul, zero_add],
    calc B = A * (-1) + B : by rw [h3, zero_mul, zero_add]
    ... = f (-1) : by rw ← h
    ... = A - 1 : by rw add_sub_cancel
    ... = -1 : by rw [h3, zero_sub], },
  { right,
    rw sub_eq_zero at h3,
    rw [h3, one_mul] at h2,
    apply funext,
    intros x; simp,
    rw [h, h3, ← h2, one_mul], },
end

end solution



---- Wrapper
theorem IMO2015A2_sol :
  set_of fn_eq = {const ℤ (-1), id + 1} :=
begin
  rw set.ext_iff; simp,
  intros f; split,
  { exact solution.fn_sol f },
  { intros h,
    cases h with h h; subst h,
    exact answer.fn_answer1,
    exact answer.fn_answer2, },
end






end IMO2015A2