import algebra.order.field.defs data.set.finite tactic.ring

/-! # IMO 2008 A2 (P2) -/

namespace IMOSL
namespace IMO2008A2

/- ### Part a -/

section ring_eq

variables {R : Type*} [comm_ring R]

lemma ring_id_a1 (a b c : R) : a ^ 2 + b ^ 2 + c ^ 2 - 1
  = (a + b + c - 1) ^ 2 + (-2) * (a * b * c - (a - 1) * (b - 1) * (c - 1)) :=
  by ring

lemma ring_id_a2 {a b c : R} (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) :
  a ^ 2 + b ^ 2 + c ^ 2 - 1 = (a + b + c - 1) ^ 2 :=
  (ring_id_a1 a b c).trans $ add_right_eq_self.mpr $
    mul_eq_zero_of_right _ $ sub_eq_zero_of_eq h

end ring_eq


section field_eq

variables {F : Type*} [field F]

/-- `x/(x - 1) - 1 = 1/(x - 1)` if `x ≠ 1`. -/
lemma field_eq_a1 {x : F} (h : x ≠ 1) : x / (x - 1) - 1 = 1 / (x - 1) :=
  (div_sub_one $ sub_ne_zero_of_ne h).trans $ congr_arg2 _ (sub_sub_cancel x 1) rfl

/-- If `xyz = 1` and `a = x/(x - 1)`, `b = y/(y - 1)`, `c = z/(z - 1)`,
  then `abc = (a - 1)(b - 1)(c - 1)`. -/
lemma field_eq_a2 {x y z : F} (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (h : x * y * z = 1) :
  x / (x - 1) * (y / (y - 1)) * (z / (z - 1))
    = (x / (x - 1) - 1) * (y / (y - 1) - 1) * (z / (z - 1) - 1) :=
  by rw [field_eq_a1 hx, field_eq_a1 hy, field_eq_a1 hz, div_mul_div_comm,
    div_mul_div_comm, h, ← one_div_mul_one_div, ← one_div_mul_one_div]

end field_eq

/-- The main inequality -/
lemma ring_ineq_a {R : Type*} [linear_ordered_comm_ring R]
  {a b c : R} (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) :
  1 ≤ a ^ 2 + b ^ 2 + c ^ 2 :=
  le_of_sub_nonneg $ (sq_nonneg $ a + b + c - 1).trans_eq (ring_id_a2 h).symm


/-- Final solution, part a -/
theorem final_solution_part_a {F : Type*} [linear_ordered_field F]
  {x y z : F} (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) (h : x * y * z = 1) :
  1 ≤ (x / (x - 1)) ^ 2 + (y / (y - 1)) ^ 2 + (z / (z - 1)) ^ 2 :=
  ring_ineq_a $ field_eq_a2 hx hy hz h





/- ### Part b -/

lemma ring_id_b {R : Type*} [comm_ring R] [no_zero_divisors R] {a b c : R}
  (h : a * b * c = (a - 1) * (b - 1) * (c - 1)) (h0 : a + b + c = 1) :
  a ^ 2 + b ^ 2 + c ^ 2 = 1 :=
  eq_of_sub_eq_zero $ (ring_id_a2 h).trans $
    sq_eq_zero_iff.mpr $ sub_eq_zero_of_eq h0

section field_eq

variables {F : Type*} [field F]

lemma field_eq_b1 {t : F} (h : t ≠ 0) (h0 : t + 1 ≠ 0) :
  ((-(t + 1) / t ^ 2)) * (t / (t + 1) ^ 2) * (-(t * (t + 1))) = 1 :=
  by rw [neg_div, neg_mul, neg_mul_neg, div_mul_div_comm, ← mul_pow, mul_comm (t + 1),
    ← mul_div_right_comm, ← sq]; exact div_self (pow_ne_zero 2 $ mul_ne_zero h h0)

lemma field_eq_b2 (a : F) {b : F} (h : b ≠ 0) : (a / b) / (a / b - 1) = a / (a - b) :=
  by rw [div_div, mul_sub_one, mul_div_cancel' a h]

lemma field_eq_b3 {t : F} (h : t ≠ 0) (h0 : t + 1 ≠ 0) (h1 : t * (t + 1) + 1 ≠ 0) :
  let x := (-(t + 1) / t ^ 2), y := t / (t + 1) ^ 2, z := -(t * (t + 1)) in
  x / (x - 1) + y / (y - 1) + z / (z - 1) = 1 :=
  (congr_arg2 _ (congr_arg2 _ (field_eq_b2 _ $ pow_ne_zero 2 h)
    (field_eq_b2 _ $ pow_ne_zero 2 h0)) rfl).trans $
  by rw [← neg_add', neg_div_neg_eq, ← neg_add', neg_div_neg_eq, add_comm _ (t ^ 2),
    ← add_assoc, ← neg_sub, div_neg, add_sq', one_pow, mul_one, two_mul, ← add_assoc,
    add_sub_cancel, add_right_comm _ 1 t, sq, ← mul_add_one, ← sub_eq_add_neg,
    ← sub_div, add_sub_cancel', ← add_div, add_comm]; exact div_self h1

end field_eq


def rat_map_sol (k : ℕ) : ℚ × ℚ × ℚ :=
  (-(k.succ + 1) / k.succ ^ 2, k.succ / (k.succ + 1) ^ 2, -(k.succ * (k.succ + 1)))

lemma rat_map_sol_prod2_strict_anti : strict_anti (λ k, (rat_map_sol k).2.2) :=
  λ k m h, neg_lt_neg $ let h0 : (k.succ : ℚ) < m.succ := nat.cast_lt.mpr $ nat.succ_lt_succ h in
    mul_lt_mul h0 (add_lt_add_right h0 1).le
      (add_pos (nat.cast_pos.mpr k.succ_pos) one_pos) (m + 1).cast_nonneg
 
lemma rat_map_sol_inj : function.injective rat_map_sol :=
  λ k m h, rat_map_sol_prod2_strict_anti.injective $ congr_arg _ $ congr_arg _ h


/-- Final solution, part b -/
theorem final_solution_part_b :
  {p : ℚ × ℚ × ℚ | (p.1 ≠ 1 ∧ p.2.1 ≠ 1 ∧ p.2.2 ≠ 1) ∧ p.1 * p.2.1 * p.2.2 = 1 ∧
    (p.1 / (p.1 - 1)) ^ 2 + (p.2.1 / (p.2.1 - 1)) ^ 2 + (p.2.2 / (p.2.2 - 1)) ^ 2 = 1}.infinite :=
set.infinite_of_injective_forall_mem rat_map_sol_inj $
  λ k, let X : 0 < (1 : ℚ) := zero_lt_one' ℚ,
    h : 0 < (k.succ : ℚ) := nat.cast_pos.mpr k.succ_pos,
    h0 : (k.succ : ℚ) < k.succ + 1 := lt_add_of_pos_right _ X,
    h1 := h.trans h0, h2 := h.ne.symm, h3 := h1.ne.symm, p := rat_map_sol k in
---- First prove that the components are not equal to `1`
have p.1 ≠ 1 ∧ p.2.1 ≠ 1 ∧ p.2.2 ≠ 1 :=
  ⟨((div_neg_of_neg_of_pos (neg_lt_zero.mpr h1) (pow_pos h 2)).trans X).ne,
  div_ne_one_of_ne $ (h0.trans_le $ le_self_pow
    (le_add_of_nonneg_left $ (k + 1).cast_nonneg) (nat.succ_ne_zero 1)).ne,
  ((neg_lt_zero.mpr $ mul_pos h h1).trans X).ne⟩,
---- Back to the whole thing
⟨this, let h4 := field_eq_b1 h2 h3 in
  ⟨h4, ring_id_b (field_eq_a2 this.1 this.2.1 this.2.2 h4)
    (field_eq_b3 h2 h3 (add_pos (mul_pos h h1) X).ne.symm)⟩⟩

end IMO2008A2
end IMOSL
