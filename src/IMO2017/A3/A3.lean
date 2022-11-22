import data.fintype.card tactic.abel data.set.finite

/-! # IMO 2017 A3 -/

namespace IMOSL
namespace IMO2017A3

open function set

/-- Final solution, monoid version (the claim) -/
theorem final_solution_monoid {M : Type*} [monoid M] [fintype M]
  {x : M} (h : ∀ y : M, x * y * x = y * x * y → y = x) :
  ∃ m : ℕ, 1 < m ∧ x ^ m = x :=
begin

  ---- get some `k > n` such that `x ^ k = x ^ n`
  obtain ⟨n, k, h0, h1⟩ : ∃ n k : ℕ, n < k ∧ x ^ n = x ^ k :=
  begin
    have h0 := not_injective_infinite_finite (λ n : ℕ, x ^ n),
    simp_rw [injective, not_forall] at h0,
    rcases h0 with ⟨n, k, h0, h1⟩,
    rw [← ne.def, ne_iff_lt_or_gt, gt_iff_lt] at h1,
    wlog h1 : n < k := h1 using [n k, k n],
    exact ⟨n, k, h1, h0⟩
  end,

  ---- Now write `k = n + t` and get rid of the case `n = 0`
  rcases n.eq_zero_or_pos with rfl | h2,
  refine ⟨k + 1, nat.succ_lt_succ h0, by rw [pow_succ, ← h1, pow_zero, mul_one]⟩,
  rw lt_iff_exists_add at h0,
  rcases h0 with ⟨t, h0, rfl⟩,

  ---- Choose `m = nt + 1` and prove the equality
  refine ⟨n * t + 1, nat.succ_lt_succ (mul_pos h2 h0), h _ _⟩; clear h2,
  rw [pow_succ, ← mul_assoc (_ * x), ← pow_succ, ← pow_succ,
      ← pow_succ', ← pow_succ', ← pow_succ', ← pow_add],
  change n * t + 1 + 1 + 1 with n * t + 3,
  replace h0 : n ≤ n * t + 3 := le_trans (nat.le_mul_of_pos_right h0) le_self_add,
  generalize_hyp : n * t + 3 = d at h0 ⊢,
  generalize_hyp : n = k,

  ---- More generally, we have `x ^ d = x ^ (d + kt)` for all `d ≥ n` and `k ≥ 0` by induction
  revert k; suffices : x ^ d = x ^ (d + t),
  { intros k; induction k with k k_ih,
    rw [zero_mul, add_zero],
    rw [nat.succ_eq_one_add, one_add_mul, ← add_assoc, pow_add, ← this, ← pow_add, ← k_ih] },
  revert h0 d; apply nat.le_induction,
  exact h1,
  rintros d - h0,
  rw [add_right_comm, pow_succ, pow_succ, ← h0]
end



/-- Final solution -/
theorem final_solution {S : Type*} [fintype S] [decidable_eq S]
  {f : function.End S} (h : ∀ g : S → S, f * g * f = g * f * g → g = f) :
  range (f^[2]) = range f :=
begin
  refine subset.antisymm (range_comp_subset_range f f) _,
  rcases final_solution_monoid h with ⟨m, h1, h0⟩,
  rw [← nat.succ_le_iff, le_iff_exists_add] at h1,
  rcases h1 with ⟨c, rfl⟩,
  nth_rewrite 0 ← h0; clear h0,
  rw [pow_add, pow_succ, pow_one, iterate_succ, iterate_one],
  exact range_comp_subset_range _ (f ∘ f)
end

end IMO2017A3
end IMOSL
