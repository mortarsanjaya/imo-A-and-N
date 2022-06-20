import
  data.int.basic
  data.set.basic

namespace IMO2015A2

/--
  IMO 2015 A2

  Determine all functions f : ℤ → ℤ such that, for all x, y ∈ ℤ,
          f(x - f(y)) = f(f(x)) - f(y) - 1.

  Answer: f = -1 and f = x ↦ x + 1.

  See http://www.imo-official.org/problems/IMO2015SL.pdf
  We will follow the official solution.
-/
def fn_eq (f : ℤ → ℤ) :=
  ∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1



open function







---- All functions satisying fn_eq are described here
namespace answer

theorem fn_ans1 :
  fn_eq (const ℤ (-1)) :=
begin
  intros _ _,
  rw [const_apply, sub_self, zero_sub],
end

theorem fn_ans2 :
  fn_eq (id + 1) :=
begin
  intros _ _,
  simp only [id.def, pi.add_apply, pi.one_apply],
  rw [add_sub_add_right_eq_sub, sub_add_eq_add_sub, sub_sub],
end

end answer



---- Extra lemmas needed to solve the problem
namespace extra

lemma linear_eq_match {a b c d : ℤ} :
  (∀ x : ℤ, a * x + b = c * x + d) → a = c ∧ b = d :=
begin
  intros h,
  have h0 := h 0,
  rw [mul_zero, mul_zero, zero_add, zero_add] at h0,
  have h1 := h 1,
  rw [mul_one, mul_one, h0, add_left_inj] at h1,
  split; assumption,
end

end extra



---- We prove that there are no other functions satisfying fn_eq here
namespace solution

variable {f : ℤ → ℤ}
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  ∀ x : ℤ, f (f x) = f (x + 1) :=
begin
  intros x,
  have h := feq 0 (f 0),
  rw [zero_sub, sub_self, zero_sub] at h,
  have h0 := feq x (-f (f 0)),
  rwa [h, sub_neg_eq_add, sub_neg_eq_add, add_sub_cancel, eq_comm] at h0,
end

lemma fn_lem2 :
  ∀ x y : ℤ, f (x - f y) = f (x + 1) - f y - 1 :=
begin
  intros x y,
  have h := feq x y,
  rwa fn_lem1 feq at h,
end

lemma fn_lem3 :
  ∀ x : ℤ, f (x - 1 - f x) = -1 :=
begin
  intros x,
  have h := fn_lem2 feq (x - 1) x,
  rwa [sub_add_cancel, sub_self, zero_sub] at h,
end

lemma fn_lem4 :
  ∀ x : ℤ, f (x + 1) = f (-1) + 1 + f x :=
begin
  intros x,
  rw ← sub_eq_iff_eq_add,
  calc f (x + 1) - f x = f (x + 1) - f x - 1 + 1 : by rw sub_add_cancel
  ... = f (x - f x) + 1 : by rw ← fn_lem2 feq
  ... = f (x - f x - 1 + 1) + 1 : by rw sub_add_cancel
  ... = f (f (x - f x - 1)) + 1 : by rw ← fn_lem1 feq
  ... = f (f (x - 1 - f x)) + 1 : by rw sub_right_comm
  ... = f (-1) + 1 : by rw fn_lem3 feq,
end

lemma fn_lem5 :
  ∀ x : ℤ, f x = (f (-1) + 1) * x + f 0 :=
begin
  suffices : ∀ x n : ℤ, f (x + n) = (f (-1) + 1) * n + f x,
    intros x; rw [← zero_add x, this, zero_add],
  have h : ∀ (x : ℤ) (n : ℕ), f (x + ↑n) = (f (-1) + 1) * ↑n + f x,
  { intros x n,
    induction n with n,
    rw [int.coe_nat_zero, mul_zero, add_zero, zero_add],
    rw [int.coe_nat_succ, ← add_assoc, fn_lem4 feq, n_ih,
        ← add_assoc, add_left_inj, add_comm ↑n, mul_add, mul_one] },
  intros x n,
  cases n with n,
  rw [int.of_nat_eq_coe, h],
  rw [int.neg_succ_of_nat_eq, ← int.coe_nat_succ, mul_neg,
      eq_neg_add_iff_add_eq, ← h, neg_add_cancel_right],
end

theorem fn_sol :
  f = const ℤ (-1) ∨ f = id + 1 :=
begin
  let A := f (-1) + 1,
  let B := f 0,
  have h : ∀ x : ℤ, f x = A * x + B := by exact fn_lem5 feq,
  have h0 : A = A * A ∧ A + B = A * B + B,
  { apply extra.linear_eq_match; intros x,
    calc A * x + (A + B) = A * (x + 1) + B : by rw [mul_add, mul_one, add_assoc _ A]
    ... = f (x + 1) : by rw ← h
    ... = f (f x) : by rw ← fn_lem1 feq
    ... = A * (A * x + B) + B : by rw [h, h]
    ... = A * A * x + (A * B + B) : by rw [mul_add, add_assoc, ← mul_assoc] },
  cases h0 with h0 h1,
  rw [eq_comm, mul_left_eq_self₀] at h0,
  cases h0 with h0 h0,
  { rw [add_left_inj, h0, one_mul] at h1,
    right; apply funext; intros x,
    rw [pi.add_apply, id.def, pi.one_apply, h, h0, one_mul, ← h1] },
  { left; apply funext; intros x,
    rw [const_apply, h, h0, zero_mul, zero_add],
    calc B = A * (-1) + B : by rw [h0, zero_mul, zero_add]
    ... = f (-1) : by rw ← h
    ... = A - 1 : by rw add_sub_cancel
    ... = -1 : by rw [h0, zero_sub] },
end

end solution



---- Wrapper
theorem final_solution :
  set_of fn_eq = {const ℤ (-1), id + 1} :=
begin
  rw set.ext_iff; intros f,
  rw [set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff]; split,
  exact solution.fn_sol,
  intros h; cases h with h h; subst h,
  exact answer.fn_ans1,
  exact answer.fn_ans2,
end







end IMO2015A2
