import data.fintype.big_operators algebra.big_operators.intervals algebra.big_operators.order

/-! # IMO 2006 A2 -/

namespace IMOSL
namespace IMO2006A2

open finset

variables {F : Type*} [linear_ordered_field F]

private lemma div_sub_lt_div_sub {a b c : F} (h : 0 < a) (h0 : a < b) (h1 : b < c) :
  c / (c - a) < b / (b - a) :=
  by rwa [div_lt_div_iff (sub_pos.mpr (lt_trans h0 h1)) (sub_pos.mpr h0),
    mul_sub, mul_sub, mul_comm, sub_lt_sub_iff_left, mul_lt_mul_right h]



def a : ℕ → F := nat.strong_rec' (λ n (f : Π m, m < n → F),
    ite (n = 0) (-1) (-(univ : finset (fin n)).sum (λ i, f i i.2 / (n.succ - i))))

private lemma a_zero : a 0 = (-1 : F) :=
  by rw [a, nat.strong_rec', if_pos rfl] 

private lemma a_nonzero {n : ℕ} (h : n ≠ 0) :
  (a n : F) = - (range n).sum (λ i, a i / (n.succ - i)) :=
  by rw [← fin.sum_univ_eq_sum_range, a, nat.strong_rec', ← a, if_neg h]; refl



/-- Final solution -/
theorem final_solution {n : ℕ} (h : 0 < n) : 0 < (a n : F) :=
begin
  ---- Setup for strong induction, including the base case
  rw [← nat.succ_le_iff, le_iff_exists_add'] at h,
  rcases h with ⟨n, rfl⟩,
  induction n using nat.strong_induction_on with n n_ih,
  rcases n.eq_zero_or_pos with rfl | h,
  rw [zero_add, a_nonzero one_ne_zero, sum_range_one, a_zero, neg_div,
      neg_neg, one_div_pos, sub_pos, nat.cast_two, nat.cast_zero],
  exact two_pos,

  ---- Induction step
  have X : 0 < (n.succ.succ : F) := nat.cast_pos.mpr n.succ.succ_pos,
  rw [a_nonzero n.succ_ne_zero, neg_pos, sum_range_succ', nat.cast_zero,
      sub_zero, ← lt_neg_iff_add_neg, ← neg_div, lt_div_iff X, sum_mul],
  replace X : (a n : F) = _ := a_nonzero (ne_of_gt h),
  have X0 : (n.succ : F) ≠ 0 := nat.cast_ne_zero.mpr n.succ_ne_zero,
  rw [eq_neg_iff_add_eq_zero, ← sum_range_succ_sub_top, nat.cast_succ, add_tsub_cancel_left,
      div_one, add_sub_cancel'_right, sum_range_succ', nat.cast_zero, ← nat.cast_succ,
      sub_zero, add_eq_zero_iff_eq_neg, ← neg_div, eq_div_iff X0] at X,
  rw [← X, sum_mul]; clear X X0,
  refine sum_lt_sum_of_nonempty (nonempty_range_iff.mpr $ ne_of_gt h) (λ i h0, _),
  rw mem_range at h0,
  rw [mul_comm_div, mul_comm_div, mul_lt_mul_left (n_ih i h0)],
  refine div_sub_lt_div_sub (nat.cast_pos.mpr i.succ_pos) _ _,
  rwa [nat.cast_lt, nat.succ_lt_succ_iff],
  rw nat.cast_lt; exact n.succ.lt_succ_self
end

end IMO2006A2
end IMOSL
