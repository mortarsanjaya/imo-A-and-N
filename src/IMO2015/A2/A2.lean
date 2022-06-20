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
  We will follow the official Solution 1.
-/
def fn_eq (f : ℤ → ℤ) :=
  ∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1







---- Extra lemmas needed to solve the problem
namespace extra

lemma fn_linear_diff {f : ℤ → ℤ} {c : ℤ} (h : ∀ x : ℤ, f (x + 1) = f x + c) :
  ∀ x : ℤ, f x = c * x + f 0 :=
begin
  suffices : ∀ (x : ℤ) (n : ℕ), f (x + ↑n) = f x + c * ↑n,
  { intros x,
    rcases int.eq_coe_or_neg x with ⟨n, h | h⟩,
    rw [← zero_add x, h, this, zero_add, add_comm],
    rw [add_comm, h, mul_neg, eq_add_neg_iff_add_eq, ← this, neg_add_self] },
  intros x n,
  induction n with n,
  rw [int.coe_nat_zero, mul_zero, add_zero, add_zero],
  rw [int.coe_nat_succ, ← add_assoc, h, n_ih, mul_add_one, add_assoc],
end

lemma linear_eq_match {a b c d : ℤ} (h : ∀ x : ℤ, a * x + b = c * x + d) :
  a = c ∧ b = d :=
begin
  have h0 := h 0,
  rw [mul_zero, mul_zero, zero_add, zero_add] at h0,
  split,
  have h1 := h 1,
  rwa [mul_one, mul_one, h0, add_left_inj] at h1,
  exact h0,
end

end extra







open function

namespace results



---- All functions satisying fn_eq are described here
section answer

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



---- We prove that there are no other functions satisfying fn_eq here
section solution

variables {f : ℤ → ℤ} (feq : fn_eq f)
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
  rw ← fn_lem1 feq,
  exact feq x y,
end

lemma fn_lem3 :
  ∀ x : ℤ, f (x - 1 - f x) = -1 :=
begin
  intros x,
  rw [fn_lem2 feq, sub_add_cancel, sub_self, zero_sub],
end

lemma fn_lem4 :
  ∀ x : ℤ, f x = (f (-1) + 1) * x + f 0 :=
begin
  apply extra.fn_linear_diff; intros x,
  rw [add_comm (f x), ← sub_eq_iff_eq_add],
  calc f (x + 1) - f x = f (x + 1) - f x - 1 + 1 : by rw sub_add_cancel
  ... = f (x - f x) + 1 : by rw ← fn_lem2 feq
  ... = f (x - f x - 1 + 1) + 1 : by rw sub_add_cancel
  ... = f (f (x - f x - 1)) + 1 : by rw ← fn_lem1 feq
  ... = f (f (x - 1 - f x)) + 1 : by rw sub_right_comm
  ... = f (-1) + 1 : by rw fn_lem3 feq,
end

theorem fn_thm :
  f = const ℤ (-1) ∨ f = id + 1 :=
begin
  let A := f (-1) + 1,
  let B := f 0,
  have h : ∀ x : ℤ, f x = A * x + B := fn_lem4 feq,
  have h0 : A = A * A ∧ A + B = A * B + B,
  { apply extra.linear_eq_match; intros x,
    calc A * x + (A + B) = A * (x + 1) + B : by rw [mul_add, mul_one, add_assoc _ A]
    ... = A * (A * x + B) + B : by rw [← h, ← fn_lem1 feq, h, h]
    ... = A * A * x + (A * B + B) : by rw [mul_add, add_assoc, ← mul_assoc] },
  cases h0 with h0 h1,
  rw [eq_comm, mul_left_eq_self₀] at h0,
  cases h0 with h0 h0,
  { right; apply funext; intros x,
    rw [add_left_inj, h0, one_mul] at h1,
    rw [pi.add_apply, id.def, pi.one_apply, h, h0, one_mul, ← h1] },
  { left; apply funext; intros x,
    rw [const_apply, h, h0, zero_mul, zero_add],
    calc B = A * (-1) + B : by rw [h0, zero_mul, zero_add]
    ... = f (-1) : by rw ← h
    ... = A - 1 : by rw add_sub_cancel
    ... = -1 : by rw [h0, zero_sub] },
end

end solution



end results







---- Final solution
theorem final_solution :
  set_of fn_eq = {const ℤ (-1), id + 1} :=
begin
  rw set.ext_iff; intros f,
  rw [set.mem_set_of_eq, set.mem_insert_iff, set.mem_singleton_iff]; split,
  exact results.fn_thm,
  intros h; cases h with h h,
  rw h; exact results.fn_ans1,
  rw h; exact results.fn_ans2,
end

end IMO2015A2
