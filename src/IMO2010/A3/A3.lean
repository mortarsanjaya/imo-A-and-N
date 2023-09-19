import algebra.order.ring.defs algebra.big_operators.order algebra.periodic

/-! # IMO 2010 A3 -/

namespace IMOSL
namespace IMO2010A3

open finset

variables {R : Type*} [linear_ordered_comm_ring R]

def good (c : R) (x : ℕ → R) :=
  ∀ i, x i + x (i + 1) + x (i + 2) ≤ 2 * c

def target_sum (x : ℕ → R) (n : ℕ) :=
  (range n).sum $ λ i, x i * x (i + 2) + x (i + 1) * x (i + 3)





/- ### Upper bound -/

lemma special_ineq {w x y z c : R} (hx : 0 ≤ x) (hy : 0 ≤ y)
  (h : w + x + y ≤ 2 * c) (h0 : x + y + z ≤ 2 * c) :
  w * y + x * z ≤ c ^ 2 :=
  (add_le_add
    (mul_le_mul_of_nonneg_right (le_sub_right_of_add_le $ (add_assoc w x y).symm.trans_le h) hy)
    (mul_le_mul_of_nonneg_left (le_sub_left_of_add_le h0) hx)).trans $
  by rw [mul_comm x, ← mul_add, add_comm, sub_mul, ← sq, sub_le_iff_le_add];
    exact two_mul_le_add_sq c (y + x)

lemma target_upper_bound {c : R} {x : ℕ → R} (h : ∀ i, 0 ≤ x i) (h0 : good c x) (n : ℕ) :
  target_sum x n ≤ n • c ^ 2 :=
  ((range n).sum_le_card_nsmul (λ i, x i * x (i + 2) + x (i + 1) * x (i + 3)) (c ^ 2) $
    λ i _, special_ineq (h _) (h _) (h0 _) (h0 _)).trans_eq $
  congr_arg2 has_smul.smul (card_range n) rfl





/- ### Equality case -/

def good_seq (c : R) (n : ℕ) : R := ite (even n) c 0

lemma even_add_two {n : ℕ} : even (n + 2) ↔ even n :=
  nat.even_add.trans $ iff_true_right even_two

lemma good_seq_two_mul (c : R) (n : ℕ) : good_seq c (2 * n) = c :=
  if_pos $ even_two_mul n

lemma good_seq_two_mul_add_one (c : R) (n : ℕ) : good_seq c (2 * n + 1) = 0 :=
  if_neg $ cast (congr_arg not $ congr_arg even $ nat.bit1_val n) (nat.not_even_bit1 n)

lemma good_seq_nonneg {c : R} (h : 0 ≤ c) (n : ℕ) : 0 ≤ good_seq c n :=
  (ite_eq_or_eq (even n) c 0).elim (λ h0, h.trans_eq h0.symm) ge_of_eq
  
lemma good_seq_periodic (c : R) : function.periodic (good_seq c) 2 :=
  λ n, if_congr even_add_two rfl rfl

lemma good_seq_is_good {c : R} (h : 0 ≤ c) : good c (good_seq c) :=
begin
  intros i; rw [good_seq, good_seq, good_seq],
  by_cases h0 : even i,
  ---- `i` is even
  { rw [if_pos h0, if_neg _, if_pos (even_add_two.mpr h0), add_zero, ← two_mul],
    rwa [nat.even_add_one, not_not] },
  ---- `i` is odd
  { rw [if_neg h0, zero_add, if_pos (nat.even_add_one.mpr h0), if_neg, add_zero, two_mul],
    exact le_add_of_nonneg_left h,
    exact cast (congr_arg not $ iff_iff_eq.mp even_add_two.symm) h0 }
end

lemma good_seq_target_sum (c : R) : ∀ n, target_sum (good_seq c) (2 * n) = (2 * n) • c ^ 2
| 0 := (zero_nsmul $ c ^ 2).symm
| (n+1) := by rw [target_sum, nat.mul_succ, sum_range_succ, sum_range_succ, ← target_sum,
    good_seq_target_sum, good_seq_two_mul, good_seq_two_mul_add_one, zero_mul, add_zero, zero_add,
    add_assoc (2 * n), bit1, add_add_add_comm, ← nat.mul_succ, good_seq_two_mul, ← nat.mul_succ,
    good_seq_two_mul, ← sq, ← succ_nsmul', ← succ_nsmul', add_assoc, ← nat.mul_succ]





/- ### Final solution -/

/-- Final solution -/
theorem final_solution (n : ℕ) {c : R} (h : 0 ≤ c) :
  is_greatest ((λ x : ℕ → R, target_sum x (2 * n)) ''
    {x | (∀ i, 0 ≤ x i) ∧ function.periodic x (2 * n) ∧ good c x})
  ((2 * n) • c ^ 2) :=
⟨⟨good_seq c, ⟨good_seq_nonneg h, cast (congr_arg _ $ mul_comm n 2)
  ((good_seq_periodic c).nat_mul n), good_seq_is_good h⟩, good_seq_target_sum c n⟩,
λ r h0, exists.elim h0 $ λ x h0, h0.2.symm.trans_le $
  target_upper_bound h0.1.1 h0.1.2.2 (2 * n)⟩

end IMO2010A3
end IMOSL
