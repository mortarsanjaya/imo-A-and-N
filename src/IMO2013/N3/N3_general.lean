import data.set.finite data.pnat.basic tactic.ring

/-! # IMO 2013 N3, Generalized Version -/

namespace IMOSL
namespace IMO2013N3

variables {S : Type*} [linear_order S]

def good (f : ℕ+ → S) (n : ℕ+) := f (n ^ 4 + n ^ 2 + 1) = f ((n + 1) ^ 4 + (n + 1) ^ 2 + 1)



/-- Proof of the identity `(n + 1)⁴ + (n + 1)² + 1 = (n² + n + 1)((n + 1)² + (n + 1) + 1)`. -/
private lemma special_identity (n : ℕ+) :
  ((n + 1) ^ 2) ^ 2 + (n + 1) ^ 2 + 1 = (n ^ 2 + n + 1) * ((n + 1) ^ 2 + (n + 1) + 1) :=
  pnat.eq $ by simp only [positive.coe_one, pnat.mul_coe, pnat.pow_coe, pnat.add_coe]; ring



/-- Final solution -/
theorem final_solution_general {f : ℕ+ → S} (h : ∀ a b : ℕ+, f (a * b) = max (f a) (f b)) :
  set.infinite (set_of (good f)) :=
begin
  ---- Set `g(n) = f(n^2 + n + 1)` and re-interpret in terms of `g` instead of `f`
  apply set.infinite_of_not_bdd_above; rintros ⟨N, h0⟩,
  simp_rw [upper_bounds, set.mem_set_of, good] at h0,
  let T := λ n : ℕ+, n ^ 2 + n + 1,
  replace h : ∀ n : ℕ+, (f ∘ T) ((n + 1) ^ 2) = max ((f ∘ T) n) ((f ∘ T) (n + 1)) :=
    λ n, by simp_rw [function.comp_app, T]; rw [special_identity, h],
  replace h0 : ∀ n : ℕ+, (f ∘ T) (n ^ 2) = (f ∘ T) ((n + 1) ^ 2) → n ≤ N :=
    λ n, by simp_rw [function.comp_app, T, ← pow_mul]; rw [two_mul, ← bit0]; exact @h0 n,
  generalize_hyp : f ∘ T = g at h h0,
  clear f T,

  ---- For all `n ≥ N`, `g(n) ≤ g(n + 1)` implies `g(n + 1) < g(n + 2)`
  replace h0 : ∀ n, N ≤ n → g n ≤ g (n + 1) → g (n + 1) < g (n + 1 + 1) :=
  begin
    intros n h1 h2; contrapose! h0,
    refine ⟨n + 1, _, pnat.lt_add_one_iff.mpr h1⟩,
    rw [h, max_eq_right h2, h, max_eq_left h0],
  end,

  ---- There exists `C ≥ N` such that `g(C) ≤ g(C + 1)`
  obtain ⟨C, h1, h2⟩ : ∃ C : ℕ+, N ≤ C ∧ g C ≤ g (C + 1) :=
  begin
    replace h : g (N + 1) ≤ g ((N + 1) ^ 2) :=
      by rw h; exact le_max_right (g N) (g (N + 1)),
    contrapose! h; rw [sq, mul_add_one, add_comm _ (N + 1)],
    generalize : (N + 1) * N = k,
    induction k using pnat.case_strong_induction_on with k h1,
    exact h (N + 1) (le_of_lt (N.lt_add_right 1)),
    rw ← add_assoc; refine lt_trans (h _ _) (h1 k (le_refl k)),
    rw add_assoc; exact le_of_lt (N.lt_add_right (1 + k))
  end,
  
  ---- Reduce to showing `g(C + 1) < g(C + 1 + k)` for all `k > 0`
  replace h := h C,
  rw [max_eq_right h2, sq, mul_add_one, add_comm _ (C + 1)] at h,
  generalize_hyp : (C + 1) * C = k at h,
  revert h; apply ne_of_gt; revert k,

  ---- Final step via two inductions
  replace h0 : ∀ k : ℕ+, g (C + k) < g (C + k + 1) :=
  begin
    intros k; induction k using pnat.case_strong_induction_on with k h3,
    exact h0 C h1 h2,
    rw ← add_assoc,
    exact h0 _ (le_trans h1 (le_of_lt (C.lt_add_right k))) (le_of_lt (h3 k (le_refl k)))
  end,

  clear h1 h2 N,
  intros k; induction k using pnat.case_strong_induction_on with k h,
  exact h0 1,
  rw ← add_assoc; refine lt_trans (h k (le_refl k)) _,
  rw add_assoc; exact h0 (1 + k)
end

end IMO2013N3
end IMOSL
