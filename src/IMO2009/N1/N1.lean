import data.zmod.basic extra.periodic.big_operators data.nat.periodic

/-! # IMO 2009 N1 (P1) -/

namespace IMOSL
namespace IMO2009N1

open function finset extra



/-- Generalized version with commutative monoids -/
theorem final_solution_general_monoid {M : Type*} [comm_monoid M] {k : ℕ} (hk : 0 < k)
  {a : ℕ → M} (h : periodic a k) (h0 : ∀ i : ℕ, a i * a i.succ = a i) :
  ∀ i j : ℕ, a i = a j :=
begin
  suffices : ∀ i : ℕ, a i = (range k).prod a,
    intros i j; rw [this, this],
  intros i; rw ← periodic_prod_const h i,
  clear h; cases k with k k,
  exfalso; exact lt_irrefl 0 hk,
  clear hk; induction k with k k_ih,
  rw [prod_range_one, zero_add],
  rw [k_ih, prod_range_succ, prod_range_succ, prod_range_succ, mul_assoc, nat.succ_add, h0]
end

/-- Generalized version with commutative rings -/
theorem final_solution_general_ring {R : Type*} [comm_ring R] {k : ℕ} (hk : 0 < k)
  {a : ℕ → R} (h : periodic a k) (h0 : ∀ i : ℕ, a i * (a i.succ - 1) = 0) :
  ∀ i j : ℕ, a i = a j :=
  final_solution_general_monoid hk h
    (λ i, by rw [← sub_eq_zero, ← mul_sub_one]; exact h0 i)

/-- Generalized version with integers using divisibility -/
theorem final_solution_int_div {k : ℕ} (hk : 0 < k) {a : ℕ → ℤ} (h : periodic a k)
  (n : ℕ) (h0 : ∀ i : ℕ, (n : ℤ) ∣ a i * (a i.succ - 1)) :
  ∀ i j : ℕ, (n : ℤ) ∣ a i - a j :=
begin
  intros i j; rw [← int.modeq_iff_dvd, ← zmod.int_coe_eq_int_coe_iff, eq_comm],
  revert i j; refine final_solution_general_ring hk (periodic.comp h coe) (λ i, _),
  rw [← int.cast_one, ← int.cast_sub, ← int.cast_mul, zmod.int_coe_zmod_eq_zero_iff_dvd],
  exact h0 i
end

/-- Final solution -/
theorem final_solution {k : ℕ} (hk : 0 < k) {a : ℕ → ℤ} (h : periodic a k.succ)
  (h0 : ∀ i j : ℕ, i < k.succ → j < k.succ → a i = a j → i = j) (n : ℕ)
  (h1 : ∀ i : ℕ, 0 < a i ∧ a i ≤ n) (h2 : ∀ i : ℕ, i < k → (n : ℤ) ∣ a i * (a i.succ - 1)) :
  ¬(n : ℤ) ∣ a k * (a 0 - 1) :=
begin
  intros h3,
  refine zero_ne_one (h0 0 1 k.succ_pos (nat.succ_lt_succ hk) _),
  rw ← sub_eq_zero,
  refine int.eq_zero_of_abs_lt_dvd (final_solution_int_div k.succ_pos h n _ 0 1) _,
  { intros i,
    rw [← periodic.map_mod_nat h, ← periodic.map_mod_nat h i.succ,
        nat.succ_eq_add_one i, ← nat.mod_add_mod, periodic.map_mod_nat h (i % _ + 1)],
    have h4 := nat.mod_lt i k.succ_pos,
    rw [nat.lt_succ_iff, le_iff_lt_or_eq] at h4,
    cases h4 with h4 h4,
    exact h2 _ h4,
    rwa [h4, ← nat.succ_eq_add_one, ← zero_add k.succ, h] },
  { suffices : ∀ i j : ℕ, a i - a j < n,
    { rw abs_sub_lt_iff; split,
      exacts [this _ _, this _ _] },
    intros i j,
    rw sub_lt_iff_lt_add,
    refine lt_of_le_of_lt (h1 i).2 _,
    rw lt_add_iff_pos_right; exact (h1 j).1 }
end

end IMO2009N1
end IMOSL
