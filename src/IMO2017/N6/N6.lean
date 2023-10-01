import algebra.big_operators.multiset.basic data.set.finite data.nat.prime data.nat.fib

/-! # IMO 2017 N6 -/

namespace IMOSL
namespace IMO2017N6

structure nice (S : multiset ℚ) : Prop :=
(pos : ∀ q : ℚ, q ∈ S → 0 < q)
(sum_eq_int : ∃ k : ℤ, S.sum = k)
(sum_inv_eq_int : ∃ k : ℤ, (S.map has_inv.inv).sum = k)

def good (n : ℕ) := {S : multiset ℚ | S.card = n ∧ nice S}.infinite





open multiset

/-! ## Preliminaries -/

lemma nice_one_cons {S : multiset ℚ} (h : nice S) : nice (1 ::ₘ S) :=
{ pos := λ q h0, (mem_cons.mp h0).elim (λ h0, one_pos.trans_eq h0.symm) (h.pos q),
  sum_eq_int := exists.elim h.sum_eq_int $ λ k h0,
    ⟨k + 1, (S.sum_cons 1).trans $ (add_comm _ _).trans $ h0.symm ▸ (int.cast_add k 1).symm⟩,
  sum_inv_eq_int := exists.elim h.sum_inv_eq_int $ λ k h0,
    ⟨k + 1, (S.map_cons has_inv.inv 1).symm ▸ (sum_cons _ _).trans
      ((add_comm _ _).trans $ h0.symm ▸ (int.cast_add k 1).symm) ⟩ }

lemma good_succ {n : ℕ} (h : good n) : good n.succ :=
  set.infinite_of_inj_on_maps_to (λ S h0 T h1, (cons_inj_right (1 : ℚ)).mp)
    (λ S h0, let h0 : S.card = n ∧ nice S := h0 in
      h0.imp (λ h0, h0 ▸ S.card_cons 1) nice_one_cons) h

lemma good_of_good_le {n : ℕ} (h : good n) : ∀ k : ℕ, n ≤ k → good k :=
  nat.le_induction h (λ k h0, good_succ)

lemma good_succ_not_good_imp {n : ℕ} (h : good n.succ) (h0 : ¬good n) (k : ℕ) :
  good k ↔ n.succ ≤ k :=
  ⟨λ h1, nat.succ_le_of_lt $ lt_of_not_le $ λ h2, h0 $ good_of_good_le h1 n h2,
    good_of_good_le h k⟩





/-! ## `2` is not good -/

lemma rat_inv_denom {q : ℚ} (h : 0 < q) : (q⁻¹.denom : ℤ) = q.num :=
  (@rat.inv_def' q).symm ▸ rat.denom_div_eq_of_coprime (rat.num_pos_iff_pos.mpr h) q.cop.symm

lemma denom_eq_of_add_eq_int : ∀ {q r : ℚ} {k : ℤ}, q + r = k → q.denom = r.denom :=
suffices ∀ {q r : ℚ} {k : ℤ}, q + r = k → q.denom ∣ r.denom,
  from λ q r k h, (this h).antisymm $ this ((add_comm r q).trans h),
λ q r k h, (eq_add_neg_of_add_eq h).symm ▸ (rat.add_denom_dvd _ _).trans
  (dvd_of_eq $ (rat.coe_int_denom k).symm ▸ (one_mul _).trans r.denom_neg_eq_denom)

lemma eq_of_add_and_inv_add_eq_int {q r : ℚ} {k m : ℤ}
  (h : 0 < q) (h0 : 0 < r) (h1 : q + r = k) (h2 : q⁻¹ + r⁻¹ = m) : q = r :=
  @rat.num_denom q ▸ @rat.num_denom r ▸ congr_arg2 rat.mk
    (rat_inv_denom h ▸ rat_inv_denom h0 ▸ denom_eq_of_add_eq_int h2 ▸ rfl)
    (congr_arg _ $ denom_eq_of_add_eq_int h1)
 
lemma nice_card_two_imp {S : multiset ℚ} (h : S.card = 2) (h0 : nice S) :
  ∃ q : ℚ, S = replicate 2 q :=
begin
  rw card_eq_two at h,
  rcases h with ⟨x, y, rfl⟩,
  rw insert_eq_cons at h0 ⊢,
  refine ⟨x, _⟩,
  rw [replicate_succ, cons_inj_right, replicate_one, singleton_inj],
  rcases h0 with ⟨h0, ⟨k, h1⟩, ⟨m, h2⟩⟩,
  rw [sum_cons, sum_singleton] at h1,
  rw [map_cons, map_singleton, sum_cons, sum_singleton] at h2,
  exact (eq_of_add_and_inv_add_eq_int (h0 x $ mem_cons_self x _)
    (h0 y $ mem_cons_of_mem $ mem_singleton_self y) h1 h2).symm
end

lemma two_mul_eq_nat_imp_denom_dvd {q : ℚ} {k : ℤ} (h : 2 • q = k) :
  q.denom = 1 ∨ q.denom = 2 :=
begin
  rw [← @rat.num_denom q, two_nsmul, ← rat.add_mk, ← two_mul, rat.mk_eq_div] at h,
  replace h := congr_arg rat.denom h,
  have h0 : (q.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr q.pos,
  rw [rat.coe_int_denom, rat.denom_div_cast_eq_one_iff _ _ h0,
      int.coe_nat_dvd_left, int.nat_abs_mul, int.nat_abs_bit0,
      int.nat_abs_one, nat.coprime.dvd_mul_right q.cop.symm] at h,
  exact (nat.dvd_prime nat.prime_two).mp h
end

lemma nice_replicate_two_imp {q : ℚ} (h : nice (replicate 2 q)) :
  q = 2⁻¹ ∨ q = 1 ∨ q = 2 :=
begin
  rcases h with ⟨h, ⟨k, h0⟩, ⟨m, h1⟩⟩,
  replace h : 0 < q := h q (mem_replicate.mpr ⟨nat.succ_ne_zero 1, rfl⟩),
  replace h0 := two_mul_eq_nat_imp_denom_dvd ((sum_replicate 2 q).trans h0),
  rw [map_replicate, sum_replicate] at h1,
  replace h1 := two_mul_eq_nat_imp_denom_dvd h1,
  rw [← int.coe_nat_inj', rat_inv_denom h, nat.cast_one,
      ← int.coe_nat_inj', rat_inv_denom h, nat.cast_two] at h1,

  ---- `1/2`, `1/1`, `2/2`, and `2/1`, respectively.
  refine h1.elim (λ h1, h0.symm.imp (λ h0, _) (λ h0, or.inl _))
    (λ h1, or.inr $ h0.symm.imp (λ h0, _) (λ h0, _)),
  { rw [← q.num_div_denom, h1, h0, int.cast_one, nat.cast_two, one_div] },
  { rw [← q.num_div_denom, h1, h0, int.cast_one, nat.cast_one, div_one] },
  { rw [← q.num_div_denom, h1, h0, int.cast_two, nat.cast_two, div_self (two_ne_zero' ℚ)] },
  { rw [← q.num_div_denom, h1, h0, int.cast_two, nat.cast_one, div_one] }
end

/-- This is actually an equality, but one direction is enough. -/
lemma set_of_nice_card_two_subseteq : {S : multiset ℚ | S.card = 2 ∧ nice S} ⊆
  {replicate 2 2⁻¹, replicate 2 1, replicate 2 2} :=
begin
  intros S h,
  rcases nice_card_two_imp h.1 h.2 with ⟨q, rfl⟩,
  rw [set.mem_insert_iff, set.mem_insert_iff],
  exact (nice_replicate_two_imp h.2).imp (congr_arg _)
    (λ h0, h0.imp (congr_arg _) (congr_arg _))
end

lemma not_good_two : ¬good 2 :=
  set.not_infinite.mpr $ (((set.finite_singleton _).insert _).insert _).subset
    set_of_nice_card_two_subseteq





/-! ## `3` is good -/

lemma fib_formula1 : ∀ n : ℕ, (2 * n + 2).fib ^ 2 + 1 = (2 * n + 1).fib * (2 * n + 3).fib
| 0 := rfl
| (n+1) := by rw [@nat.fib_add_two (2 * (n + 1) + 1), mul_add (nat.fib _), add_assoc,
    nat.fib_add_two, sq, add_mul, add_right_comm, add_left_inj, nat.mul_succ, mul_add,
    add_right_comm, ← sq, fib_formula1, ← add_mul, ← nat.fib_add_two]

lemma fib_formula2 (n : ℕ) :
  (2 * n + 3).fib ^ 2 + (2 * n + 1).fib ^ 2 + 1 = 3 * ((2 * n + 1).fib * (2 * n + 3).fib) :=
  by rw [nat.fib_add_two, sq, add_mul, add_assoc, add_assoc, add_comm, nat.succ_mul 2,
    add_left_inj, mul_add, add_add_add_comm, ← sq, fib_formula1, sq, ← add_mul,
    add_comm (2 * n + 1 + 1).fib, ← nat.fib_add_two, mul_comm, ← two_mul]

lemma fib_formula3 (n : ℕ) :
  rat.mk ((2 * n + 3).fib.succ + 1) (2 * n + 1).fib.succ
    + rat.mk ((2 * n + 1).fib.succ + 1) (2 * n + 3).fib.succ
    = 3 :=
begin
  have X : ∀ r : ℕ, (r.succ : ℤ) ≠ 0 := λ r, int.coe_nat_ne_zero_iff_pos.mpr r.succ_pos,
  rw [rat.add_def (X _) (X _), rat.mk_eq_div, div_eq_iff],
  work_on_goal 2 { rw int.cast_ne_zero, exact (mul_ne_zero (X _) (X _)) },
  change (3 : ℚ) with bit1 ↑(1 : ℕ),
  rw [← nat.cast_bit1, ← nat.cast_mul, int.cast_coe_nat, ← nat.cast_mul, ← nat.cast_succ,
      ← nat.cast_succ, ← nat.cast_mul, ← nat.cast_mul, ← nat.cast_add, int.cast_coe_nat,
      nat.cast_inj, nat.succ_mul, ← sq, (2 * n + 1).fib.succ.succ_mul, ← sq, add_add_add_comm,
      nat.succ_eq_add_one, nat.succ_eq_add_one, add_sq', add_sq', one_pow, mul_one, mul_one,
      add_add_add_comm (_ + 1), ← mul_add, add_add_add_comm _ 1, ← add_assoc _ 1,
      fib_formula2, add_add_add_comm _ 1, add_add_add_comm, ← nat.mul_succ, add_assoc _ 1,
      ← nat.succ_eq_one_add, add_assoc, add_comm _ (2 * _), ← nat.succ_mul, ← mul_add,
      nat.succ_eq_add_one, add_assoc, ← add_assoc, ← add_one_mul, ← mul_add_one]
end



def nice_fib_multiset (n : ℕ) : multiset ℚ :=
  ({(2 * n + 3).fib.succ, (2 * n + 1).fib.succ, 1} : multiset ℕ).map $
    λ r : ℕ, rat.mk r ((2 * n + 3).fib.succ + (2 * n + 1).fib.succ + 1)

lemma nice_fib_multiset_card (n : ℕ) : (nice_fib_multiset n).card = 3 :=
  by rw [nice_fib_multiset, card_map, insert_eq_cons,
    card_cons, insert_eq_cons, card_cons, card_singleton]

lemma nice_fib_multiset_mem_pos (n : ℕ) {q : ℚ} (h : q ∈ nice_fib_multiset n) : 0 < q :=
begin
  rw [nice_fib_multiset, mem_map] at h,
  rcases h with ⟨r, h, rfl⟩,
  rw [← nat.cast_add, ← nat.cast_succ, rat.mk_eq_div, int.cast_coe_nat, int.cast_coe_nat],
  refine div_pos (nat.cast_pos.mpr _) (nat.cast_pos.mpr $ nat.succ_pos _),
  rw [insert_eq_cons, mem_cons, insert_eq_cons, mem_cons, mem_singleton] at h,
  rcases h with rfl | rfl | rfl; exact nat.succ_pos _
end

lemma nice_fib_multiset_sum (n : ℕ) : (nice_fib_multiset n).sum = 1 :=
begin
  rw [nice_fib_multiset, insert_eq_cons, map_cons, insert_eq_cons,
      map_cons, sum_cons, sum_cons, map_singleton, sum_singleton, ← rat.add_mk,
      ← rat.add_mk, nat.cast_one, ← add_assoc, rat.mk_eq_div],
  refine div_self _,
  rw [int.cast_ne_zero, ← nat.cast_add, ← nat.cast_succ, nat.cast_ne_zero],
  exact nat.succ_ne_zero _
end

lemma nice_fib_multiset_inv_sum (n : ℕ) :
  ((nice_fib_multiset n).map has_inv.inv).sum
    = ((2 * n + 3).fib.succ + (2 * n + 1).fib.succ + 6 : ℤ) :=
  let X : ∀ r : ℕ, ((r.succ : ℤ) : ℚ) ≠ 0 :=
    λ r, int.cast_ne_zero.mpr (int.coe_nat_ne_zero_iff_pos.mpr r.succ_pos) in
  by rw [nice_fib_multiset, insert_eq_cons, map_cons, map_cons, sum_cons,
    insert_eq_cons, map_cons, map_cons, sum_cons, map_singleton,
    map_singleton, sum_singleton, rat.inv_def, rat.inv_def, rat.inv_def,
    add_assoc, rat.add_mk, rat.mk_eq_div, div_self (X _), add_left_comm,
    add_left_comm ↑(2 * n + 3).fib.succ, rat.add_mk, rat.mk_eq_div, div_self (X _),
    nat.cast_one, ← rat.coe_int_eq_mk, ← add_assoc, add_add_add_comm, fib_formula3,
    add_left_comm, ← add_assoc, int.cast_add, int.cast_one, int.cast_add _ 6,
    ← add_assoc, add_right_comm, int.cast_bit0, add_comm _ (bit0 _), add_left_inj,
    int.cast_bit1, int.cast_one, ← bit0, add_right_comm, ← bit1, bit0]

lemma nice_fib_multiset_is_nice (n : ℕ) : nice (nice_fib_multiset n) :=
  ⟨λ q, nice_fib_multiset_mem_pos n,
  ⟨1, nice_fib_multiset_sum n⟩,
  ⟨(2 * n + 3).fib.succ + (2 * n + 1).fib.succ + 6, nice_fib_multiset_inv_sum n⟩⟩

lemma nice_fib_multiset_inj : function.injective nice_fib_multiset :=
suffices function.injective (λ n : ℕ, ((nice_fib_multiset n).map has_inv.inv).sum),
from λ m n h, this $ let X := congr_arg (λ S : multiset ℚ, (S.map has_inv.inv).sum) h in X,
strict_mono.injective $ strict_mono_nat_of_lt_succ $ λ n, begin
  rw [nice_fib_multiset_inv_sum, nice_fib_multiset_inv_sum, int.cast_lt, add_lt_add_iff_right,
      nat.mul_succ, add_comm, add_lt_add_iff_right, int.coe_nat_lt, nat.succ_lt_succ_iff],
  refine nat.fib_le_fib_succ.trans_lt (nat.fib_add_two_strict_mono _),
  rw [add_assoc, lt_add_iff_pos_right],
  exact nat.succ_pos 2
end

lemma good_three : good 3 :=
  set.infinite_of_injective_forall_mem nice_fib_multiset_inj $
  λ n, ⟨nice_fib_multiset_card n, nice_fib_multiset_is_nice n⟩





/-! ## Final solution -/

/-- Final solution -/
theorem final_solution {n : ℕ} : good n ↔ 3 ≤ n :=
  good_succ_not_good_imp good_three not_good_two n

end IMO2017N6
end IMOSL
