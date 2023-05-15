import
  extra.periodic.big_operators
  data.nat.periodic
  data.nat.prime
  algebra.big_operators.order
  tactic.fin_cases

/-! # IMO 2018 A2 (P2) -/

namespace IMOSL
namespace IMO2018A2

open finset function extra

variables {R : Type*} [linear_ordered_comm_ring R]

def good (a : ℕ → R) := ∀ i : ℕ, a i * a (i + 1) + 1 = a (i + 2)



section extra

lemma sum_nonneg_eq_zero {M : Type*} [linear_ordered_add_comm_group M] {a : ℕ → M}
  (h : ∀ i : ℕ, 0 ≤ a i) {n : ℕ} (h0 : (range n).sum a = 0) {j : ℕ} (h1 : j < n) : a j = 0 :=
begin
  revert h1 j; induction n with n n_ih,
  intros j h1; exfalso; exact not_le_of_lt h1 j.zero_le,
  rw [sum_range_succ, add_eq_zero_iff_eq_neg] at h0,
  have h1 : 0 ≤ (range n).sum (λ (x : ℕ), a x) := sum_nonneg (λ i _, h i),
  rw [h0, neg_nonneg] at h1,
  replace h1 := le_antisymm h1 (h n),
  rw [h1, neg_zero] at h0,
  intros j h2,
  rw [nat.lt_succ_iff, le_iff_eq_or_lt] at h2,
  rcases h2 with rfl | h2,
  exacts [h1, n_ih h0 h2]
end

lemma periodic_shift {α M : Type*} [add_comm_monoid M] {f : M → α} {c : M}
    (h : periodic f c) (d : M) : periodic (λ m, f (m + d)) c :=
  λ m, by simp only []; rw [add_right_comm, h]

lemma sq_add_one_ne_self (x : R) : x * x + 1 ≠ x :=
begin
  intros h,
  apply not_lt.mpr (sq_nonneg (2 * x - 1)),
  rw ← eq_sub_iff_add_eq at h,
  rw [sub_sq, mul_pow, sq, sq, h, mul_one, one_pow, mul_sub_one, mul_assoc, sub_sub_cancel_left],
  norm_num
end

end extra



/-- A good periodic function must be 3-periodic. -/
private lemma periodic_to_periodic3 {a : ℕ → R} (h : good a)
  {n : ℕ} (h0 : 0 < n) (h1 : periodic a n) : periodic a 3 :=
begin
  have h2 : (range n).sum (λ i, 2 * a (i + 2) ^ 2 + (a (i + 3) - a i) ^ 2) =
    (range n).sum (λ i, a (i + 3) ^ 2 + a i ^ 2 + 2 * (a (i + 2) - a i)) :=
  begin
    apply congr_arg; funext i,
    rw [add_comm, sub_sq', ← add_sub_right_comm, add_sub_assoc, add_right_inj,
        mul_assoc, ← mul_sub, mul_right_inj' (two_ne_zero : (2 : R) ≠ 0),
        sub_eq_sub_iff_sub_eq_sub, ← sub_one_mul, mul_comm, sq, ← sub_one_mul],
    dsimp only [good] at h,
    conv at h { find (_ = _) { rw ← eq_sub_iff_add_eq } },
    rw [← h, mul_assoc, bit0, ← add_assoc, h]
  end,
  repeat { rw sum_add_distrib at h2 },
  rw [← mul_sum, ← mul_sum] at h2,
  repeat { rw periodic_sum_const (periodic.comp h1 (λ x, x ^ 2)) at h2 },
  dsimp only [comp] at h2,
  rw [← two_mul, add_right_inj, sum_sub_distrib, periodic_sum_const h1, sub_self, mul_zero] at h2,
  intros i,
  replace h2 := sum_nonneg_eq_zero (λ i, sq_nonneg (a (i + 3) - a i)) h2 (i.mod_lt h0),
  rwa [pow_eq_zero_iff, periodic.map_mod_nat h1, ← periodic.map_mod_nat h1,
       nat.mod_add_mod, periodic.map_mod_nat h1, sub_eq_zero] at h2,
  exact two_pos
end



/-- One example of a good function. -/
def good_ex (i : ℕ) : R := ite (i % 3 = 0) 2 (-1)

private lemma good_ex_good : good (good_ex : ℕ → R)  :=
begin
  intros i; dsimp only [good_ex],
  rw [← nat.mod_add_mod, ← nat.mod_add_mod i],
  let p : fin 3 := ⟨i % 3, i.mod_lt three_pos⟩,
  fin_cases p using hp,
  all_goals {
    rw fin.ext_iff at hp,
    simp [p] at hp,
    rw hp; norm_num }
end

private lemma good_shift {a : ℕ → R} (h : good a) (k : ℕ) : good (λ i, a (i + k)) :=
  λ i, by simp only []; rw [add_right_comm, h, add_right_comm]



/-- Solution of the underlying equation for a good 3-periodic function. -/
private lemma good_solution {a b c : R}
    (h : a * b + 1 = c) (h0 : b * c + 1 = a) (h1 : c * a + 1 = b) :
  (a, b, c) = (2, -1, -1) ∨ (a, b, c) = (-1, 2, -1) ∨ (a, b, c) = (-1, -1, 2) :=
begin
  have h2 : ∀ x y z : R, x * y + 1 = z → y * z + 1 = x → y = -1 ∨ x = z :=
  begin
    intros x y z h h0,
    replace h0 := congr_arg2 (λ x y, x - y) h h0; simp only [] at h0,
    rwa [add_sub_add_right_eq_sub, mul_comm, ← mul_sub, ← neg_sub x,
         ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero] at h0
  end,
  rcases h2 a b c h h0 with rfl | rfl,
  { rcases h2 _ _ _ h0 h1 with rfl | rfl,
    rw [← h0, mul_neg_one, neg_neg]; left; refl,
    rw [← h, mul_neg_one, neg_neg]; right; right; refl },
  { rcases h2 _ _ _ h0 h1 with rfl | rfl,
    rw [← h1, mul_neg_one, neg_neg]; right; left; refl,
    exfalso; exact sq_add_one_ne_self b h }
end

/-- Characterization of all good 3-periodic functions. -/
private lemma good_period3_iff (a : ℕ → R) : (good a ∧ periodic a 3) ↔
  a = good_ex ∨ a = (λ i, good_ex (i + 1)) ∨ a = λ i, good_ex (i + 2) :=
begin
  split,
  /- The → direction is quite costly, but with a relatively shorter code -/
  { rintros ⟨h, h0⟩,
    obtain (h1 | h1 | h1) : (a 0, a 1, a 2) = (2, -1, -1) ∨
      (a 0, a 1, a 2) = (-1, 2, -1) ∨ (a 0, a 1, a 2) = (-1, -1, 2) :=
    begin
      apply good_solution,
      replace h := h 0,
      rwa [zero_add, zero_add] at h,
      replace h := h 1,
      rwa [bit0, ← add_assoc, ← periodic.map_mod_nat h0 3] at h,
      replace h := h 2,
      rwa [← periodic.map_mod_nat h0 3, ← periodic.map_mod_nat h0 4] at h
    end,
    left,
    work_on_goal 2 { right; right },
    work_on_goal 3 { right; left },
    all_goals {
      rw [prod.mk.inj_iff, prod.mk.inj_iff] at h1,
      rcases h1 with ⟨h1, h2, h3⟩,
      funext i; dsimp only [good_ex],
      rw ← periodic.map_mod_nat h0,
      try { rw ← nat.mod_add_mod },
      let p : fin 3 := ⟨i % 3, i.mod_lt three_pos⟩,
      fin_cases p using hp,
      all_goals {
        rw fin.ext_iff at hp,
        simp [p] at hp,
        rw hp; assumption } } },
  { have h : periodic good_ex 3 := λ i, if_congr (by rw i.add_mod_right 3) rfl rfl,
    rintros (rfl | rfl | rfl); split,
    exacts [good_ex_good, h, good_shift good_ex_good 1, periodic_shift h 1,
            good_shift good_ex_good 2, periodic_shift h 2] }
end



/-- Final solution, extra version -/
theorem final_solution_extra {n : ℕ} (h : 0 < n) {a : ℕ → R} (h0 : periodic a n) :
  good a ↔ a = good_ex ∨ a = (λ i, good_ex (i + 1)) ∨ a = λ i, good_ex (i + 2) :=
begin
  rw ← good_period3_iff a,
  symmetry; apply and_iff_left_of_imp,
  intros h1; exact periodic_to_periodic3 h1 h h0
end

/-- Final solution, extra version, case 3 ∤ n -/
theorem final_solution_extra_not3dvd {n : ℕ} (h : 0 < n) (h0 : ¬ 3 ∣ n)
  {a : ℕ → R} (h1 : periodic a n) : ¬good a :=
begin
  replace h0 := (or_iff_left h0).mp (nat.coprime_or_dvd_of_prime nat.prime_three n),
  rw nat.coprime_comm at h0,
  intros h2,
  replace h1 : periodic a 1 :=
  begin
    cases nat.exists_mul_mod_eq_one_of_coprime h0 (by norm_num) with q h3,
    have h4 := periodic_to_periodic3 h2 h h1,
    intros i,
    rw [← h3, ← periodic.map_mod_nat h4, nat.add_mod_mod, periodic.map_mod_nat h4,
        ← periodic.map_mod_nat h1, nat.add_mul_mod_self_left, periodic.map_mod_nat h1]
  end,
  replace h2 := h2 0,
  rw [bit0, ← add_assoc, h1 (0 + 1), h1] at h2,
  exact sq_add_one_ne_self (a 0) h2
end

/-- Final solution, original version -/
theorem final_solution (n : ℕ) (h : 0 < n) : (∃ a : ℕ → R, good a ∧ periodic a n) ↔ 3 ∣ n :=
begin
  split,
  { rintros ⟨a, h0, h1⟩,
    by_contra h2,
    exact final_solution_extra_not3dvd h h2 h1 h0 },
  { rintros ⟨n, rfl⟩,
    use good_ex; split,
    exact good_ex_good,
    intros i,
    simp only [good_ex, nat.add_mul_mod_self_left] }
end

end IMO2018A2
end IMOSL
