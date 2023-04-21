import data.fintype.card data.set.finite

/-! # IMO 2017 A3 -/

namespace IMOSL
namespace IMO2017A3

section finite_npow

variables {M : Type*} [has_pow M ℕ] [fintype M] (x : M)

private lemma npow_not_inj_of_finite : ∃ a b : ℕ, a ≠ b ∧ x ^ a = x ^ b := 
  finite.exists_ne_map_eq_of_infinite (λ n : ℕ, x ^ n)

private lemma npow_not_inj_of_finite2 : ∃ a b : ℕ, a < b ∧ x ^ a = x ^ b :=
  by rcases npow_not_inj_of_finite x with ⟨a, b, h, h0⟩;
    exact (lt_or_gt_of_ne h).elim (λ h, ⟨a, b, h, h0⟩) (λ h, ⟨b, a, h, h0.symm⟩)

private lemma npow_not_inj_of_finite3 : ∃ n k : ℕ, 0 < k ∧ x ^ (n + k) = x ^ n :=
begin
  rcases npow_not_inj_of_finite2 x with ⟨a, b, h, h0⟩,
  rw lt_iff_exists_add at h; rcases h with ⟨k, h, rfl⟩,
  exact ⟨a, k, h, h0.symm⟩
end

end finite_npow


section monoid_npow

variables {M : Type*} [monoid M] {x : M} {n k : ℕ} (h : x ^ (n + k) = x ^ n)
include h

private lemma npow_mul_add_eq_of_npow_add_eq : ∀ t : ℕ, x ^ (n + t * k) = x ^ n
| 0 := congr_arg (λ c, x ^ c) $ (congr_arg (has_add.add n) (zero_mul k)).trans $ add_zero n
| (t+1) := by rw [add_one_mul, ← add_assoc, pow_add, npow_mul_add_eq_of_npow_add_eq, ← pow_add, h]

private lemma npow_add_eq_of_npow_add_eq_of_le {n0 : ℕ} (h0 : n ≤ n0) : x ^ (n0 + k) = x ^ n0 :=
  by rw le_iff_exists_add at h0; rcases h0 with ⟨c, rfl⟩; rw [add_right_comm, pow_add, h, pow_add]

end monoid_npow



/-- Final solution, monoid version (the claim) -/
theorem final_solution_monoid {M : Type*} [monoid M] [fintype M]
  {x : M} (h : ∀ y : M, x * y * x = y * x * y → y = x) :
  ∃ m : ℕ, 1 < m ∧ x ^ m = x :=
begin
  ---- Take some `k > 0` and `n ≥ 0` such that `x^{n + k} = x^n`.
  obtain ⟨n, k, h0, h1⟩ := npow_not_inj_of_finite3 x,

  ---- Remove the case `n = 0`.
  rcases n.eq_zero_or_pos with rfl | h2,
  refine ⟨k + 1, nat.succ_lt_succ h0, _⟩,
  rw zero_add at h1,
  rw [pow_succ, h1, pow_zero, mul_one],

  ---- Claim that `m = nk + 1` works by reducing to `x^{2nk + 3} = x^{nk + 3}`.
  refine ⟨n * k + 1, nat.succ_lt_succ (nat.mul_pos h2 h0), h _ _⟩,

  ---- Now prove that `x^{2nk + 3} = x^{nk + 3}`.
  replace h := npow_add_eq_of_npow_add_eq_of_le
    (npow_mul_add_eq_of_npow_add_eq h1 n) (nat.le_mul_of_pos_right h0),
  generalize_hyp : n * k = d at h ⊢; clear h0 h1 h2 n k,
  rw [mul_assoc, pow_mul_comm', mul_assoc, ← pow_succ, ← pow_add,
      add_add_add_comm, pow_add x (d + d), h, ← pow_add]
end



/-- Final solution -/
theorem final_solution {S : Type*} [fintype S] [decidable_eq S]
  {f : function.End S} (h : ∀ g : S → S, f * g * f = g * f * g → g = f) :
  set.range (f ∘ f) = set.range f :=
  (set.range_comp_subset_range f f).antisymm
(begin
  replace h := final_solution_monoid h,
  rcases h with ⟨m, h, h0⟩,
  nth_rewrite 0 ← h0,
  rw [← nat.succ_le_iff, le_iff_exists_add] at h,
  rcases h with ⟨c, rfl⟩,
  rw pow_add; exact set.range_comp_subset_range _ (f ∘ f)
end)

end IMO2017A3
end IMOSL
