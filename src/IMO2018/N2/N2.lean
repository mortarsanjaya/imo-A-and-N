import data.int.modeq algebra.big_operators.basic

/-! # IMO 2018 N2 -/

namespace IMOSL
namespace IMO2018N2

open finset

private lemma add_modeq_mul_add_one {n a b : ℤ} (h : a ≡ 1 [ZMOD n]) (h0 : b ≡ 1 [ZMOD n]) :
  a + b ≡ a * b + 1 [ZMOD n ^ 2] :=
  by rw [int.modeq_iff_dvd, sq, add_comm, ← sub_sub_sub_eq, ← one_sub_mul, ← mul_one_sub];
    exact mul_dvd_mul h.dvd h0.dvd


variables {ι : Type*} [decidable_eq ι] {s : finset ι}

private lemma prod_one_modeq_one_mod {n : ℤ} {f : ι → ℤ} (h : ∀ i ∈ s, f i ≡ 1 [ZMOD n]) :
  s.prod f ≡ 1 [ZMOD n] :=
begin
  induction s using finset.induction with i s h0 h1,
  refl,
  rw [prod_insert h0, ← int.mul_one 1],
  exact (h i $ mem_insert_self i s).mul (h1 $ λ j h2, h j $ mem_insert_of_mem h2)
end

private lemma prod_one_mod_add_card_modeq_sum_add_one
  {n : ℤ} {f : ι → ℤ} (h : ∀ i ∈ s, f i ≡ 1 [ZMOD n]) :
  s.prod f + s.card ≡ s.sum f + 1 [ZMOD n ^ 2] :=
begin
  induction s using finset.induction with i s h0 h1, refl,
  rw [prod_insert h0, sum_insert h0, card_insert_of_not_mem h0,
      nat.cast_succ, ← add_assoc, add_right_comm],
  have h2 : ∀ j : ι, j ∈ s → f j ≡ 1 [ZMOD n] := λ j h2, h j (mem_insert_of_mem h2),
  refine ((add_modeq_mul_add_one (h i $ mem_insert_self i s)
    (prod_one_modeq_one_mod h2)).symm.add_right _).trans _,
  rw [add_assoc, add_assoc]; exact (h1 h2).add_left _
end

private lemma prod_one_mod_modeq_one_mod_sq
  {n : ℤ} {f : ι → ℤ} (h : ∀ i ∈ s, f i ≡ 1 [ZMOD n]) (h0 : s.sum f ≡ s.card [ZMOD n ^ 2]) :
  s.prod f ≡ 1 [ZMOD n ^ 2] :=
  ((prod_one_mod_add_card_modeq_sum_add_one h).trans
    (by rw add_comm; exact h0.add_left 1)).add_right_cancel' s.card







/-- Final solution -/
theorem final_solution {n : ℤ} {f : ι → ι → ℤ}
  (h : ∀ (i ∈ s) (j ∈ s), f i j ≡ 1 [ZMOD n])
  (h0 : ∀ i ∈ s, s.sum (f i) ≡ s.card [ZMOD n ^ 2])
  (h1 : ∀ j ∈ s, s.sum (λ i, f i j) ≡ s.card [ZMOD n ^ 2]) :
  s.sum (λ i, s.prod (f i)) ≡ s.sum (λ j, s.prod (λ i, f i j)) [ZMOD n ^ 4] :=
begin
  rw [bit0, ← two_mul, pow_mul],
  refine ((prod_one_mod_add_card_modeq_sum_add_one _).symm.trans _).add_right_cancel' 1,
  exact (λ i h2, prod_one_mod_modeq_one_mod_sq (h i h2) (h0 i h2)),
  rw prod_comm; apply prod_one_mod_add_card_modeq_sum_add_one,
  exact (λ j h2, prod_one_mod_modeq_one_mod_sq (λ i h3, h i h3 j h2) (h1 j h2))
end

end IMO2018N2
end IMOSL
