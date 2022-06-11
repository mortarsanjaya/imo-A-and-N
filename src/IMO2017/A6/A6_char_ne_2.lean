import
  IMO2017.A6.A6_general
  algebra.char_p.basic
  data.real.basic
  data.set.basic
  

/-
  Solution of 2017 A6 for the case char(F) ≠ 2.

    Solution, continuing from the general case:
  From f(x + 1) = f(x) - 1, we know that f(x + n) = f(x) - n ∀ x ∈ F, n ∈ ℤ.
  In particular, for n ∈ ℤ, f(x) = n iff x = 1 - n.
  Now, plugging in y = -1 yields f(2 f(x)) + f(x) + 1 = f(-x) for all x ∈ F.

  In particular, for any x, y ∈ F, f(x) = f(y) implies f(-x) = f(-y).
  On the other hand, this implies
    f(x - y) = f(-xy) - f(f(x) f(-y)) = f(-xy) - f(f(-x) f(y)) = f(y - x).
  Finally, for any t ∈ F, f(t) = f(-t) implies
    f(2 f(t)) + 1 = 0 → f(2 f(t)) = -1 → 2 f(t) = 2 → f(t) = 1 → t = 0.
  Thus x - y = 0 → x = y, proving that f is indeed injective.
  Note that 2 f(t) = 2 → f(t) = 1 works only because char(F) ≠ 2.

    Implementation details:
  1. We do not need the whole f(x) = n ↔ x = 1 - n result.
     We actually only need f(-1) = 2, f(x) = -1 → x = 2, and f(x) = 1 → x = 0.
     In fact, we will write the first one as f(-1) = 1 + 1.

  2. We will prove f(t) = f(-t) ↔ t = 0 instead of f(t) = f(-t) → t = 0.
     We will also prove this result before f(x) = f(y) → f(x - y) = f(y - x).
     In particular we can combine the latter step directly into injectivity.
-/

namespace IMO2017A6

universe u







namespace case_char_ne_2

open function

variable {F : Type u}
variable [field F]



---- All functions satisfying fn_eq in case char(F) ≠ 2
namespace answer

lemma fn_ans1 :
  fn_eq (0 : F → F) :=
begin
  intros _ _,
  rw [pi.zero_apply, pi.zero_apply, pi.zero_apply, add_zero],
end

lemma fn_ans2 :
  fn_eq (1 - id : F → F) :=
begin
  intros _ _,
  simp only [id.def, pi.one_apply, pi.sub_apply],
  ring,
end

lemma fn_ans3 :
  fn_eq (id - 1 : F → F) :=
begin
  rw ← neg_sub,
  exact general.fn_thm1 fn_ans2,
end


end answer



---- Injectivity result for char(F) ≠ 2, implying no other possible functions satisfying fn_eq
namespace solution

variable {f : F → F}
variable feq : fn_eq f
include feq

lemma fn_lem1 :
  f 0 = 1 → ∀ x : F, f (x - 1) = f x + 1 :=
begin
  intros h x,
  rw [← sub_eq_iff_eq_add, ← general.fn_lem4_1 feq h, sub_add_cancel],
end

lemma fn_lem2 :
  f 0 = 1 → ∀ x : F, f (f x * (1 + 1)) + f x + 1 = f (-x) :=
begin
  intros h x,
  have h0 : f (-1) = 1 + 1 :=
    by rwa [← sub_eq_iff_eq_add, ← general.fn_lem4_1 feq h, neg_add_self, h],
  rw [← h0, add_assoc, ← fn_lem1 feq h, sub_eq_add_neg, feq, mul_neg_one],
end

lemma fn_lem3 (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → ∀ x : F, f x = f (-x) ↔ x = 0 :=
begin
  intros h x,
  have X : f ≠ 0,
  { intros h1,
    rw [h1, pi.zero_apply] at h,
    exact zero_ne_one h },
  have h0 := fn_lem2 feq h x,
  rw [add_right_comm, ← eq_sub_iff_add_eq, ← fn_lem1 feq h] at h0,
  calc f x = f (-x) ↔ f (-x) - f x = 0 : by rw [eq_comm, sub_eq_zero]
  ... ↔ f (f x * (1 + 1) - 1) = 0 : by rw h0
  ... ↔ f x * (1 + 1) - 1 = 1 : by rw general.fn_thm3 feq X
  ... ↔ f x * (1 + 1) = 1 + 1 : by rw sub_eq_iff_eq_add
  ... ↔ f x = 1 : _
  ... ↔ f (x + 1) = 0 : by rw [← sub_eq_zero, general.fn_lem4_1 feq h]
  ... ↔ x = 0 : by rw [general.fn_thm3 feq X, add_left_eq_self],
  ---- Solve f(x) (1 + 1) = 1 + 1 ↔ f x = 1
  { rw mul_left_eq_self₀,
    apply or_iff_left; intros h1,
    apply char_ne_2,
    apply char_p.ring_char_of_prime_eq_zero,
    exact nat.prime_two,
    rw [nat.cast_bit0, nat.cast_one, ← h1]; refl },
end

lemma fn_lem4 (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → injective f :=
begin
  intros h x y h0,
  rw [← add_neg_eq_zero, ← fn_lem3 feq char_ne_2 h, neg_add, neg_neg],
  have h1 : f (-x) = f (-y) := by rw [← fn_lem2 feq h, h0, fn_lem2 feq h],
  have h2 := feq x (-y),
  rwa [h0, ← h1, mul_neg, ← neg_mul, mul_comm, ← feq (-x) y, add_right_inj] at h2,
end

theorem fn_sol (char_ne_2 : ring_char F ≠ 2) :
  f 0 = 1 → f = 1 - id :=
begin
  intros h,
  apply general.fn_thm4 feq h,
  exact fn_lem4 feq char_ne_2 h,
end

end solution



---- Wrapper
theorem IMO2017A6_sol_char_ne_2 (char_ne_2 : ring_char F ≠ 2) :
  set_of fn_eq = ({0, 1 - id, id - 1} : set (F → F)) :=
begin
  rw set.ext_iff; intros f,
  rw set.mem_set_of_eq; simp only [set.mem_insert_iff, set.mem_singleton_iff],
  split,
  { intros h,
    by_cases h0 : f = 0,
    left; exact h0,
    right,
    have h1 := general.fn_lem3_3 h h0,
    rw sq_eq_one_iff at h1,
    cases h1 with h1 h1,
    left; exact solution.fn_sol h char_ne_2 h1,
    right,
    rw [← neg_sub, eq_neg_iff_eq_neg, eq_comm],
    apply solution.fn_sol (general.fn_thm1 h) char_ne_2,
    rwa [pi.neg_apply, h1, neg_neg] },
  { intros h,
    rcases h with h | h | h; subst h,
    exact answer.fn_ans1,
    exact answer.fn_ans2,
    exact answer.fn_ans3 },
end



end case_char_ne_2



---- Case F = ℝ
theorem IMO2017A6_sol_R :
  set_of fn_eq = ({0, 1 - id, id - 1} : set (ℝ → ℝ)) :=
begin
  apply case_char_ne_2.IMO2017A6_sol_char_ne_2,
  rw [ring_char.eq_zero, ne_comm],
  exact two_ne_zero,
end







end IMO2017A6
