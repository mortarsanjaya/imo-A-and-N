import data.int.modeq algebra.big_operators.fin

/-! # IMO 2018 N2 -/

namespace IMOSL
namespace IMO2018N2

open finset

private lemma prod_one_mod_eq_one_mod {n : ℤ} {k : ℕ}
    {f : fin k → ℤ} (h : ∀ i : fin k, f i ≡ 1 [ZMOD n]) :
  univ.prod f ≡ 1 [ZMOD n] :=
begin
  induction k with k k_ih,
  rw fin.prod_univ_zero,
  rw [fin.prod_univ_cast_succ, ← mul_one (1 : ℤ)],
  exact int.modeq.mul (k_ih (λ i, h (fin.cast_succ i))) (h _)
end

private lemma prod_one_mod_add_size_eq_sum_add_one_mod_sq {n : ℤ} {k : ℕ}
    {f : fin k → ℤ} (h : ∀ i : fin k, f i ≡ 1 [ZMOD n]) :
  univ.prod f + k ≡ univ.sum f + 1 [ZMOD n^2] :=
begin
  induction k with k k_ih,
  rw [fin.prod_univ_zero, fin.sum_univ_zero, nat.cast_zero, add_comm],
  rw [fin.prod_univ_cast_succ, fin.sum_univ_cast_succ, nat.cast_succ, add_right_comm],
  have h0 : ∀ i : fin k, f (fin.cast_succ i) ≡ 1 [ZMOD n] := λ i, h (fin.cast_succ i),
  refine int.modeq.trans _ (int.modeq.add_right _ (k_ih h0)),
  replace h0 := prod_one_mod_eq_one_mod h0,
  replace h := h (fin.last k),
  generalize_hyp : univ.prod (λ (i : fin k), f (fin.cast_succ i)) = X at h0 ⊢,
  generalize_hyp : f (fin.last k) = Y at h ⊢,
  rw [int.modeq_iff_dvd, ← neg_sub, dvd_neg] at h h0 ⊢,
  rw [add_right_comm, ← add_assoc, add_right_comm, add_sub_add_right_eq_sub, ← sub_sub,
      add_sub_right_comm, ← mul_sub_one, add_sub_right_comm, sub_add, ← sub_one_mul, sq],
  exact mul_dvd_mul h0 h
end



/-- Final solution -/
theorem final_solution {n : ℕ} {f : fin n → fin n → ℤ} (h : ∀ i j : fin n, f i j ≡ 1 [ZMOD n])
    (h0 : ∀ i : fin n, univ.sum (f i) ≡ n [ZMOD n^2])
    (h1 : ∀ j : fin n, univ.sum (λ i, f i j) ≡ n [ZMOD n^2]) :
  univ.sum (λ i, univ.prod (f i)) ≡ univ.sum (λ j, univ.prod (λ i, f i j)) [ZMOD n^4] :=
begin
  replace h0 : ∀ i : fin n, univ.prod (f i) ≡ 1 [ZMOD n^2] :=
    λ i, int.modeq.add_left_cancel (h0 i).symm (by rw add_comm;
      exact prod_one_mod_add_size_eq_sum_add_one_mod_sq (h i)),
  replace h1 : ∀ j : fin n, univ.prod (λ i, f i j) ≡ 1 [ZMOD n^2] :=
    λ j, int.modeq.add_left_cancel (h1 j).symm (by rw add_comm;
      exact prod_one_mod_add_size_eq_sum_add_one_mod_sq (λ i, h i j)),
  rw [bit0, ← mul_two, pow_mul],
  apply int.modeq.add_right_cancel' 1,
  refine int.modeq.trans (prod_one_mod_add_size_eq_sum_add_one_mod_sq h0).symm _,
  rw finset.prod_comm; exact prod_one_mod_add_size_eq_sum_add_one_mod_sq h1
end

end IMO2018N2
end IMOSL
