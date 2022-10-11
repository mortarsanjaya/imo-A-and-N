import data.rat.default tactic.fin_cases

/-! # IMO 2013 N6 -/

namespace IMOSL
namespace IMO2013N6

open function

def fn_eq (f : ℚ → ℤ) := ∀ (x : ℚ) (a : ℤ) (b : ℕ+), f ((x + a) / b) = f (((f x : ℚ) + a) / b)



section extra

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

lemma floor_eq_floor_iff (x y : α) : ⌊x⌋ = ⌊y⌋ ↔ (∀ k : ℤ, ↑k ≤ x ↔ ↑k ≤ y) :=
  ⟨λ h k, by rw [← int.le_floor, h, int.le_floor],
   λ h, le_antisymm (int.le_floor.mpr ((h _).mp (int.floor_le x)))
                    (int.le_floor.mpr ((h _).mpr (int.floor_le y)))⟩

end extra



section results

variables {f : ℚ → ℤ} (feq : fn_eq f)
include feq

private lemma lem1 (h : f 0 = f 1) : ∃ C : ℤ, f = const ℚ C :=
begin
  suffices : ∀ (n : ℕ) (a : ℤ) (b : ℕ+), f (a / b) = f ((a + n) / b),
  { use f 0; ext x; rw const_apply,
    induction x using rat.num_denom_cases_on with a b h0 h1,
    lift b to ℕ+ using h0,
    rw [← rat.coe_int_div_eq_mk, ← coe_coe, ← coe_coe],
    cases le_total 0 a with h0 h0,
    { lift a to ℕ using h0,
      replace h1 := this a 0 b,
      rw [int.cast_zero, zero_div, zero_add] at h1,
      rw [← coe_coe, ← h1] },
    { rw ← neg_nonneg at h0,
      lift (-a) to ℕ using h0 with x h0,
      replace h1 := this x a b,
      rw [h1, ← int.cast_coe_nat, h0, int.cast_neg, add_neg_self, zero_div] } },
  intros n; induction n with n n_ih; intros a b,
  rw [nat.cast_zero, add_zero],
  have h1 := feq 0 a b,
  rw [zero_add, h, ← feq, add_comm, ← int.cast_one, ← int.cast_add] at h1,
  rw [h1, n_ih, int.cast_add, nat.cast_succ, add_right_comm, add_assoc, int.cast_one]
end

private lemma lem2 (h : f 0 ≠ f 1) (m : ℤ) : f m = m :=
begin
  apply le_antisymm; rw ← not_lt; intros h0,
  { lift (f m - m) to ℕ+ using (by rwa sub_pos) with k h1,
    replace feq := feq m (-m) k,
    rw [← int.cast_add, add_neg_self, int.cast_zero, zero_div, ← int.cast_add,
        ← sub_eq_add_neg, ← h1, coe_coe, int.cast_coe_nat, ← coe_coe, div_self] at feq,
    exacts [h feq, by rw [coe_coe, nat.cast_ne_zero]; exact pnat.ne_zero k] },
  { lift (m - f m) to ℕ+ using (by rwa sub_pos) with k h1,
    replace feq := feq m (-f m) k,
    rw [← int.cast_add, ← sub_eq_add_neg, ← h1, coe_coe, int.cast_coe_nat, ← coe_coe,
        div_self, ← int.cast_add, add_neg_self, int.cast_zero, zero_div, eq_comm] at feq,
    exacts [h feq, by rw [coe_coe, nat.cast_ne_zero]; exact pnat.ne_zero k] }
end

private lemma lem3 (h : ∀ m : ℤ, f m = m) : f (1 / 2) = 0 ∨ f (1 / 2) = 1 :=
begin
  cases le_or_lt (f (1 / 2)) 0 with h0 h0,
  { have h1 : 0 < 1 - 2 * f (1 / 2) := by rw sub_pos;
      exact lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos zero_le_two h0) one_pos,
    lift 1 - 2 * f (1 / 2) to ℕ+ using h1 with b h1,
    replace feq := feq (1 / 2) (-f (1 / 2)) b,
    left; rw int.cast_neg at feq; convert feq using 2,
    rw [← sub_eq_add_neg, eq_div_iff, div_sub', coe_coe, ← int.cast_coe_nat, h1,
        int.cast_sub, int.cast_mul, int.cast_one, int.cast_two, div_mul_comm, mul_one],
    exact two_ne_zero,
    rw [coe_coe, nat.cast_ne_zero]; exact b.ne_zero,
    rw [add_neg_self, zero_div, eq_comm, ← int.cast_zero, h] },
  { have h1 : 0 < 2 * f (1 / 2) - 1 := begin
      rw [int.lt_iff_add_one_le, zero_add] at h0,
      rw [sub_pos, int.lt_iff_add_one_le, ← mul_one (1 + 1 : ℤ), ← bit0, mul_le_mul_left],
      exacts [h0, two_pos]
    end,
    lift 2 * f (1 / 2) - 1 to ℕ+ using h1 with b h1,
    replace feq := feq (1 / 2) (f (1 / 2) - 1) b,
    have h2 : (b : ℚ) ≠ 0 := by rw [coe_coe, nat.cast_ne_zero]; exact b.ne_zero,
    right; convert feq using 2,
    rw [eq_div_iff h2, div_add', coe_coe, ← int.cast_coe_nat, h1, int.cast_sub, int.cast_sub,
        sub_mul, add_sub_left_comm, int.cast_one, mul_two (1 : ℚ), int.cast_mul, sub_add_cancel',
        ← sub_eq_add_neg, int.cast_two, mul_comm (2 : ℚ), div_mul_comm, mul_one],
    exact two_ne_zero,
    rw [← int.cast_add, ← add_sub_assoc, ← two_mul, ← h1, coe_coe, int.cast_coe_nat,
        ← coe_coe b, div_self h2, eq_comm, ← int.cast_one, h] }
end

private lemma lem4 (h : ∀ m : ℤ, f m = m) (h0 : f (1 / 2) = 0)
  (a : ℕ) (b : ℕ+) (h1 : a < b) : f (a / b) = 0 :=
begin
  revert a h1; induction b using pnat.case_strong_induction_on with b b_ih; intros a h1,
  rw [pnat.one_coe, nat.lt_one_iff] at h1,
  rw [h1, nat.cast_zero, zero_div, ← int.cast_zero, h],
  rw [pnat.add_coe, pnat.one_coe, nat.lt_add_one_iff, le_iff_lt_or_eq] at h1,
  suffices : ∀ a : ℕ, a < b → f (a / ↑(b + 1)) = 0,
  { rcases h1 with h1 | rfl,
    exact this a h1,
    rcases eq_or_ne b 1 with rfl | h1,
    rw [coe_coe, pnat.add_coe, pnat.one_coe, nat.cast_add, nat.cast_one, ← bit0, h0],
    replace h1 := pnat.exists_eq_succ_of_ne_one h1,
    rcases h1 with ⟨k, rfl⟩,
    replace this := this 1 (by rw [pnat.add_coe, pnat.one_coe]; exact pnat.lt_add_left 1 k),
    rw nat.cast_one at this,
    replace feq := feq (1 / ↑(k + 1 + 1)) k (k + 1),
    replace b_ih := b_ih (k + 1) (le_refl _) k
      (by rw [pnat.add_coe, pnat.one_coe]; exact pnat.lt_add_right k 1),
    rw [this, int.cast_zero, zero_add, coe_coe k, ← coe_coe, b_ih,
        div_add', div_div, mul_comm ↑(k + 1 + 1), ← div_div] at feq,
    convert feq; rw eq_div_iff,
    simp only [pnat.one_coe, nat.cast_add, pnat.add_coe, nat.cast_one, coe_coe],
    generalize : ((k : ℕ) : ℚ) = m,
    rw [mul_add_one, mul_add_one, add_comm (1 : ℚ), add_assoc, mul_comm],
    all_goals { apply ne_of_gt, rw [coe_coe, nat.cast_pos], exact pnat.pos _ } },
  clear h1 a; intros a h1,
  replace feq := feq (a / b) a (b + 1),
  replace b_ih := b_ih b (le_refl b) a h1,
  suffices : ((b : ℚ)⁻¹ + 1) / ↑(b + 1) = (b : ℚ)⁻¹,
    rwa [b_ih, int.cast_zero, zero_add, ← coe_coe, div_eq_mul_inv (a : ℚ),
         ← mul_add_one, mul_div_assoc, this, ← div_eq_mul_inv, b_ih, eq_comm] at feq,
  simp only [pnat.one_coe, nat.cast_add, pnat.add_coe, nat.cast_one, coe_coe],
  generalize h : ((b : ℕ) : ℚ) = k,
  replace h : 0 < k := by rw [← h, nat.cast_pos]; exact pnat.pos b,
  rw [inv_eq_one_div, div_add_one, add_comm, div_div, div_mul_left],
  exacts [ne_of_gt (add_pos h one_pos), ne_of_gt h]
end

private lemma lem5 (h : ∀ m : ℤ, f m = m) (h0 : f (1 / 2) = 0) : f = int.floor :=
begin
  suffices : ∀ x : ℚ, ⌊x⌋ = 0 → f x = 0,
  { ext x,
    replace feq := feq (x - ⌊x⌋) ⌊x⌋ 1,
    rwa [coe_coe (1 : ℕ+), pnat.one_coe, nat.cast_one, div_one, div_one,
         sub_add_cancel, this (x - ⌊x⌋), int.cast_zero, zero_add, h] at feq,
    rw [int.floor_sub_int, sub_self] },
  intros x h1,
  induction x using rat.num_denom_cases_on with a b h2 h3; clear h3,
  lift b to ℕ+ using h2,
  rw [← rat.coe_int_div_eq_mk, int.cast_coe_nat] at h1 ⊢,
  have h2 : 0 < ((b : ℕ) : ℚ) := nat.cast_pos.mpr b.pos,
  rw [int.floor_eq_iff, int.cast_zero, zero_add, div_lt_one h2, le_div_iff h2,
      zero_mul, int.cast_nonneg, ← int.cast_coe_nat, int.cast_lt, ← coe_coe] at h1,
  cases h1 with h3 h1,
  lift a to ℕ using h3,
  rw [coe_coe, nat.cast_lt] at h1,
  rw [← coe_coe, ← coe_coe, lem4 feq h h0 a b h1]
end

end results



/-- Final solution -/
theorem final_solution (f : ℚ → ℤ) : fn_eq f ↔
  ((∃ C : ℤ, f = const ℚ C) ∨ f = int.floor ∨ f = int.ceil) :=
begin
  split,
  { intros feq,
    cases eq_or_ne (f 0) (f 1) with h h,
    left; exact lem1 feq h,
    right; replace h := lem2 feq h,
    cases lem3 feq h with h0 h0,
    left; exact lem5 feq h h0,
    right; suffices : (λ x, -f (-x)) = int.floor,
    { ext x; convert congr_arg has_neg.neg (congr_fun this (-x)),
      rw [neg_neg, neg_neg] },
    refine lem5 (λ x a b, _) (λ m, _) _,
    rw [neg_inj, ← neg_div, ← neg_div, neg_add, neg_add,
        int.cast_neg, neg_neg, ← int.cast_neg, feq],
    rw [← int.cast_neg, h, neg_neg],
    rw [neg_eq_zero, ← h 0],
    convert feq (1 / 2) (-1) 1; field_simp,
    rw [bit0, neg_add, ← add_assoc, add_neg_self, zero_add],
    rw [h0, int.cast_one, add_neg_self] },
  suffices : fn_eq int.floor,
  { rintros (⟨C, rfl⟩ | rfl | rfl),
    intros x a b; rw const_apply,
    exact this,
    intros x a b,
    replace this := this (-x) (-a) b,
    rwa [int.cast_neg, ← neg_add, neg_div, int.floor_neg, int.floor_neg,
         int.cast_neg, ← neg_add, neg_div, int.floor_neg, neg_inj] at this },
  intros x a b,
  rw floor_eq_floor_iff; intros k,
  have h : 0 < (b : ℚ) := by rw [coe_coe, nat.cast_pos]; exact b.pos,
  rw [le_div_iff h, le_div_iff h, ← sub_le_iff_le_add, ← sub_le_iff_le_add, coe_coe,
      ← int.cast_coe_nat, ← coe_coe b, ← int.cast_mul, ← int.cast_sub, int.cast_le, int.le_floor]
end

end IMO2013N6
end IMOSL
