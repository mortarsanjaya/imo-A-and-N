import algebra.big_operators.ring algebra.big_operators.order tactic.ring

/-! # IMO 2010 A2 -/

namespace IMOSL
namespace IMO2010A2

open finset



section comm_ring_ineq

variables {R : Type*} [linear_ordered_comm_ring R]

private theorem special_identity (x : R) :
  4 * x ^ 3 - x ^ 4 = 6 * x ^ 2 - 4 * x + 1 - ((x - 1) ^ 2) ^ 2 :=
  by ring

variables {ι : Type*} [decidable_eq ι] 

theorem sq_sum_le_sum_sq {s : finset ι} {x : ι → R} (h : ∀ i : ι, i ∈ s → 0 ≤ x i) :
  s.sum (λ i, x i ^ 2) ≤ s.sum x ^ 2 :=
begin
  induction s using finset.induction with j s s_ih1 s_ih2,
  rw [sum_empty, sum_empty, zero_pow two_pos],
  rw [sum_insert s_ih1, sum_insert s_ih1],
  replace h : 0 ≤ x j ∧ ∀ i : ι, i ∈ s → 0 ≤ x i :=
    ⟨h j (mem_insert_self j s), λ i h0, h i (mem_insert_of_mem h0)⟩,
  refine le_trans (add_le_add_left (s_ih2 h.2) _) _; clear s_ih1 s_ih2,
  rw [add_sq', le_add_iff_nonneg_right],
  exact mul_nonneg (mul_nonneg zero_le_two h.1) (sum_nonneg h.2)
end

theorem QM_AM (s : finset ι) (x : ι → R) : s.sum x ^ 2 ≤ s.card • s.sum (λ i, x i ^ 2) :=
begin
  induction s using finset.induction with j s s_ih1 s_ih2,
  rw [sum_empty, zero_pow two_pos, card_empty, zero_nsmul],
  rw [sum_insert s_ih1, sum_insert s_ih1, card_insert_of_not_mem s_ih1, succ_nsmul,
      add_sq, add_assoc, add_assoc, add_le_add_iff_left, nsmul_add, ← add_assoc,
      ← sum_const, ← sum_add_distrib, mul_sum],
  refine add_le_add (sum_le_sum (λ i junk, _)) s_ih2; clear s_ih1 s_ih2 junk,
  rw mul_right_comm; exact two_mul_le_add_sq (x i) (x j)
end

end comm_ring_ineq



variables {F : Type*} [linear_ordered_field F]

/-- An intermediate result that is more convenient to manipulate around than the main result -/
theorem final_solution_general' {ι : Type*} [decidable_eq ι] {s : finset ι} {a : ι → F}
    {σ₁ σ₂ B C S : F} (hσ₁ : s.sum a = σ₁) (hσ₂ : s.sum (λ i, a i ^ 2) = σ₂)
    (hB : 6 * σ₂ - 4 * σ₁ + s.card = B) (hC : (σ₂ - 2 * σ₁ + s.card) ^ 2 = C)
    (hS : 4 * s.sum (λ i, a i ^ 3) - s.sum (λ i, a i ^ 4) = S) :
  B - C ≤ S ∧ S ≤ B - C / s.card :=
begin
  ---- Some setups
  have X := λ (i : ι) (_ : i ∈ s), special_identity (a i),
  rw [mul_sum, ← sum_sub_distrib, sum_congr rfl X] at hS; clear X,
  rw [sum_sub_distrib, sum_add_distrib, sum_const, nsmul_one,
      sum_sub_distrib, ← mul_sum, hσ₂, ← mul_sum, hσ₁, hB] at hS,
  replace hC : s.sum (λ i, (a i - 1) ^ 2) ^ 2 = C :=
  begin
    conv_lhs {congr, congr, skip, funext, rw [sub_sq, one_pow, mul_one] },
    rw [sum_add_distrib, sum_const, nsmul_one, sum_sub_distrib, hσ₂, ← mul_sum, hσ₁, hC]
  end,
  
  ---- Now we are ready to finish proving both inequalities
  subst hS; subst hC; split; rw sub_le_sub_iff_left,
  exact sq_sum_le_sum_sq (λ i _, sq_nonneg (a i - 1)),
  rcases s.eq_empty_or_nonempty with rfl | h,
  rw [sum_empty, sum_empty, zero_pow two_pos, zero_div],
  replace h : 0 < (s.card : F) := by rwa [nat.cast_pos, card_pos],
  rw [div_le_iff' h, ← nsmul_eq_mul]; exact QM_AM s _
end

/-- Final solution, general version -/
theorem final_solution_general {ι : Type*} [decidable_eq ι] {s : finset ι} {a : ι → F}
    {σ₁ σ₂ : F} (h : s.sum a = σ₁) (h0 : s.sum (λ i, a i ^ 2) = σ₂) :
  let B := 6 * σ₂ - 4 * σ₁ + s.card, C := (σ₂ - 2 * σ₁ + s.card) ^ 2,
    S := 4 * s.sum (λ i, a i ^ 3) - s.sum (λ i, a i ^ 4) in
  B - C ≤ S ∧ S ≤ B - C / s.card :=
final_solution_general' h h0 rfl rfl rfl

/-- Final solution -/
theorem final_solution {a : fin 4 → F} (h : univ.sum a = 6) (h0 : univ.sum (λ i, a i ^ 2) = 12) :
  let S := 4 * univ.sum (λ i, a i ^ 3) - univ.sum (λ i, a i ^ 4) in 36 ≤ S ∧ S ≤ 48 :=
begin
  intros S,
  have h1 : (36 : F) = 52 - 16 := by norm_num,
  have h2 : (48 : F) = 52 - 16 / (univ : finset (fin 4)).card := by norm_num,
  have h3 : (52 : F) = 6 * 12 - 4 * 6 + (univ : finset (fin 4)).card := by norm_num,
  have h4 : (16 : F) = (12 - 2 * 6 + (univ : finset (fin 4)).card) ^ 2 := by norm_num,
  rw [h1, h2, h3, h4]; exact final_solution_general h h0
end

end IMO2010A2
end IMOSL
