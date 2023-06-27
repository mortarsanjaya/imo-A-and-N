import data.finset.basic tactic.norm_num data.nat.nth

/-! # IMO 2021 A1 -/

namespace IMOSL
namespace IMO2021A1

private lemma lem1 {n : ℕ} (hn : 0 < n)
  {x : ℕ → ℕ} (h : strict_mono x) (h0 : x (4 * n + 1) ≤ 5 ^ n) :
  ∃ i : ℕ, i < 4 * n ∧ 3 * x i.succ < x (4 * n + 1) + 2 * x i :=
begin
  contrapose! h0,
  let y : ℕ → ℕ := λ i, x (4 * n + 1) - x (4 * n - i),
  suffices : ∀ i : ℕ, i ≤ 4 * n → 3 ^ i ≤ 2 ^ i * y i,
  { replace this := this (4 * n) (le_refl _),
    rw [pow_mul, pow_mul] at this,
    replace this : (5 * 2 ^ 4) ^ n < (2 ^ 4) ^ n * y (4 * n) :=
      lt_of_lt_of_le (nat.pow_lt_pow_of_lt_left (by norm_num) hn) this,
    dsimp only [y] at this,
    rw [mul_pow, mul_comm, mul_lt_mul_left, nat.sub_self] at this,
    exacts [lt_of_lt_of_le this (nat.sub_le _ _), pow_pos (pow_pos two_pos 4) n] },
  intros i; induction i with i i_ih,
  { rintros -; dsimp only [y],
    rw [pow_zero, pow_zero, one_mul, nat.sub_zero, nat.succ_le_iff, tsub_pos_iff_lt],
    exact h (lt_add_one (4 * n)) },
  { intros h1,
    replace i_ih := i_ih (le_trans i.le_succ h1),
    rw [pow_succ', pow_succ'],
    refine le_trans (mul_le_mul_right' i_ih _) _,
    rw [mul_assoc, mul_assoc, mul_le_mul_left, mul_comm, ← not_lt],
    work_on_goal 2 { exact pow_pos two_pos i },

    clear i_ih; intros h2,
    replace h2 := add_lt_add_of_lt_of_le h2
      (h0 (4 * n - i.succ) (i.succ.sub_lt_of_pos_le _ i.succ_pos h1)),
    rw [← nat.succ_sub h1, nat.succ_sub_succ, ← mul_add, add_left_comm, ← mul_add] at h2,
    dsimp only [y] at h2,
    rw [nat.sub_add_cancel, nat.sub_add_cancel, ← one_add_mul, ← not_le] at h2,
    exact h2 (le_refl _),
    all_goals { refine h.monotone (le_trans (nat.sub_le _ _) (4 * n).le_succ) } }
end

private lemma lem2 {A : finset ℕ} {n : ℕ} (h : A.card = 4 * n + 2) : A.nonempty :=
  by rw [← finset.card_pos, h]; exact nat.add_pos_right _ two_pos



section strict_map

variables {A : finset ℕ} (h : A.nonempty)
include h

private noncomputable def finset_to_strict_map (i : ℕ) : ℕ :=
  ite (i < A.card) (nat.nth (λ a, a ∈ A) i) (A.max' h + i)

private lemma strict_map_mem {i : ℕ} (h0 : i < A.card) : finset_to_strict_map h i ∈ A :=
begin
  rw [finset_to_strict_map, if_pos h0],
  have h1 := A.finite_to_set,
  refine nat.nth_mem_of_lt_card h1 _,
  rwa A.finite_to_set_to_finset
end

private lemma strict_map_le_max {i : ℕ} (h0 : i < A.card) : finset_to_strict_map h i ≤ A.max' h :=
  A.le_max' _ (strict_map_mem h h0)

private lemma strict_map_strict_mono : strict_mono (finset_to_strict_map h) :=
begin
  intros i j h; unfold finset_to_strict_map,
  cases le_or_lt A.card i with h0 h0,
  rwa [if_neg (not_lt_of_le (le_trans h0 (le_of_lt h))),
       if_neg (not_lt_of_le h0), add_lt_add_iff_left],
  have h2 := A.finite_to_set,
  rw if_pos h0; cases lt_or_le j A.card with h1 h1,
  rw if_pos h1; refine nat.nth_strict_mono_on h2 _ _ h;
    rwa finset.finite_to_set_to_finset,
  rw if_neg (not_lt_of_le h1),
  refine lt_add_of_le_of_pos (A.le_max' _ $ nat.nth_mem_of_lt_card h2 _) (pos_of_gt h),
  rwa A.finite_to_set_to_finset
end

private lemma strict_map_image_of_mem {a : ℕ} (h0 : a ∈ A) :
  ∃ i : ℕ, i < A.card ∧ a = finset_to_strict_map h i :=
begin
  have h1 : {x | x ∈ A}.finite := {x : ℕ | x ∈ A}.to_finite,
  have h2 : nat.count (λ x, x ∈ A) a < A.card :=
    by convert nat.count_lt_card h1 h0; exact A.finite_to_set_to_finset.symm,
  refine ⟨nat.count (λ x, x ∈ A) a, h2, _⟩,
  rw [finset_to_strict_map, if_pos h2],
  refine (nat.nth_count _).symm; exact h0
end

private lemma strict_map_max : finset_to_strict_map h (A.card - 1) = A.max' h :=
begin
  refine le_antisymm (strict_map_le_max h (nat.sub_lt (finset.card_pos.mpr h) one_pos)) _,
  rw finset.max'_le_iff; intros y h0,
  rcases strict_map_image_of_mem h h0 with ⟨i, h1, rfl⟩,
  exact (strict_map_strict_mono h).monotone (nat.le_pred_of_lt h1)
end

end strict_map



/-- Final solution -/
theorem final_solution {n : ℕ} (hn : 0 < n)
  {A : finset ℕ} (h : A.card = 4 * n + 2) (h0 : A.max' (lem2 h) ≤ 5 ^ n) :
  ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a < b ∧ b < c ∧ 3 * b < c + 2 * a :=
begin
  let X := lem2 h,
  obtain ⟨i, h1, h2⟩ := lem1 hn (strict_map_strict_mono X)
    (by convert h0; rw [← strict_map_max, h, nat.add_succ_sub_one]),
  have h3 := nat.succ_lt_succ h1,
  have h4 : 4 * n + 1 < A.card := by rw h; exact (4 * n + 1).lt_succ_self,
  have h5 := lt_trans h3 h4,
  exact ⟨_, _, _, strict_map_mem _ (lt_trans i.lt_succ_self h5), strict_map_mem _ h5,
    strict_map_mem _ h4, strict_map_strict_mono _ i.lt_succ_self, strict_map_strict_mono _ h3, h2⟩
end

end IMO2021A1
end IMOSL
