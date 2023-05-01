import analysis.mean_inequalities data.multiset.fintype

/-! # IMO 2014 C2 -/

namespace IMOSL
namespace IMO2014C2

def good {α : Type*} [has_add α] (S T : multiset α) :=
  ∃ (R : multiset α) (a b : α), S = R + {a, b} ∧ T = R + multiset.replicate 2 (a + b)



section cons_last

variable {α : Type*} 

/-- Wrapper for the last element of a cons list `a :: l`, guaranteed to be non-empty. -/
private def cons_last (a : α) (l : list α) : α :=
  (list.cons a l).last (list.cons_ne_nil a l)

private lemma cons_last_nil (a : α) : cons_last a list.nil = a := rfl

private lemma cons_last_cons (a b : α) (l : list α) :
  cons_last a (list.cons b l) = cons_last b l :=
  list.last_cons (l.cons_ne_nil b)

private lemma cons_last_ne_nil (a : α) {l : list α} (h : l ≠ list.nil) :
  cons_last a l = l.last h := list.last_cons h

end cons_last





open multiset

private lemma good_card_eq {α : Type*} [has_add α] {S T : multiset α} (h : good S T) :
  T.card = S.card :=
  by rcases h with ⟨R, a, b, rfl, rfl⟩;
    rw [card_add, card_replicate, card_add, insert_eq_cons, card_cons, card_singleton]

private lemma good_chain_card_eq {α : Type*} [has_add α]
  {S : multiset α} {C : list (multiset α)} (h : list.chain good S C) :
  (cons_last S C).card = S.card :=
begin
  revert S h; induction C with T C h0,
  rintros S -; rw cons_last_nil,
  intros S h; rw list.chain_cons at h,
  rw [cons_last_cons, h0 h.2, good_card_eq h.1]
end



open_locale nnreal

private lemma multiset_AM_GM (S : multiset ℝ≥0) : S.prod ≤ (S.sum / S.card) ^ S.card :=
begin
  rcases eq_or_ne S 0 with rfl | h,
  exact le_refl 1,
  rw [ne.def, ← card_eq_zero] at h,
  rw [sum_eq_sum_coe, ← inv_mul_eq_div, finset.mul_sum],
  refine le_of_eq_of_le _
    (pow_le_pow_of_le_left (zero_le _) (nnreal.geom_mean_le_arith_mean_weighted _ _ _ _) _),
  rw [← finset.prod_pow, nonneg.coe_inv, nnreal.coe_nat_cast],
  exact (prod_eq_prod_coe S).trans (finset.prod_congr rfl $ λ x _,
    (nnreal.rpow_nat_inv_pow_nat x h).symm),
  rw [finset.sum_const, finset.card_univ, card_coe, nsmul_eq_mul],
  apply mul_inv_cancel; rwa nat.cast_ne_zero
end

private lemma good_prod_le {S T : multiset ℝ≥0} (h : good S T) : 4 * S.prod ≤ T.prod :=
begin
  rcases h with ⟨R, a, b, rfl, rfl⟩,
  simp_rw [prod_add, insert_eq_cons, prod_cons, prod_singleton],
  rw mul_left_comm; apply mul_le_mul_left',
  rw [prod_replicate, add_sq', bit0, add_mul, ← mul_assoc, add_le_add_iff_right, ← nnreal.coe_le_coe],
  simp_rw [nnreal.coe_add, nnreal.coe_pow, nnreal.coe_mul],
  rw [nnreal.coe_bit0, nnreal.coe_one, ← sub_nonneg, ← sub_sq'],
  exact sq_nonneg (a - b)
end

private lemma good_chain_le_prod {S : multiset ℝ≥0}
    {C : list (multiset ℝ≥0)} (h : list.chain good S C) :
  4 ^ C.length * S.prod ≤ (cons_last S C).prod :=
begin
  revert S h; induction C with T C h0,
  rintros S -; rw [list.length, pow_zero, one_mul, cons_last_nil S],
  intros S h; rw list.chain_cons at h,
  rw [list.length, pow_succ', mul_assoc, cons_last_cons],
  exact le_trans (mul_le_mul_left' (good_prod_le h.1) _) (h0 h.2)
end

/-- A generalized form of the final solution -/
private lemma good_chain_le_sum {S : multiset ℝ≥0}
    {C : list (multiset ℝ≥0)} (h : list.chain good S C) :
  4 ^ C.length * S.prod ≤ ((cons_last S C).sum / S.card) ^ S.card :=
  by rw ← good_chain_card_eq h; exact le_trans (good_chain_le_prod h) (multiset_AM_GM _)







/-- Final solution -/
theorem final_solution {m : ℕ} (h : 0 < m) {C : list (multiset ℝ≥0)}
  (h0 : C.length = m * 2 ^ (m - 1)) (h1 : list.chain good (replicate (2 ^ m) (1 : ℝ≥0)) C) :
  4 ^ m ≤ (cons_last (replicate (2 ^ m) (1 : ℝ≥0)) C).sum :=
begin
  have h2 := good_chain_le_sum h1,
  rw h0 at h2; clear h0 h1,
  generalize_hyp : (cons_last (replicate (2 ^ m) (1 : ℝ≥0)) C).sum = x at h2 ⊢,
  rw [prod_replicate, one_pow, mul_one, card_replicate, bit0, ← mul_two, ← sq, ← pow_mul,
      mul_left_comm, ← pow_succ, nat.sub_add_cancel h, pow_mul] at h2,
  replace h2 := le_of_pow_le_pow (2 ^ m) (zero_le (x / ↑(2 ^ m))) (pow_pos two_pos _) h2,
  rw [nat.cast_pow, nat.cast_bit0, nat.cast_one,
      le_div_iff (pow_pos _ _), ← mul_pow, two_mul, ← bit0] at h2,
  exacts [h2, two_pos]
end

end IMO2014C2
end IMOSL
