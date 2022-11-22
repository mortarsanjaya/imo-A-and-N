import data.set.finite data.pnat.basic tactic.ring

/-! # IMO 2013 N3, "Generalized" Version -/

namespace IMOSL
namespace IMO2013N3

variables {S : Type*} [linear_order S]

def good (f : ℕ+ → S) (n : ℕ+) := f (n ^ 4 + n ^ 2 + 1) = f ((n + 1) ^ 4 + (n + 1) ^ 2 + 1)



/-- A notation convenience for n² + n + 1. -/
private def T (n : ℕ+) := n ^ 2 + n + 1

/-- Proof of the identity T((n + 1)²) = T(n) T(n + 1). -/
private lemma T_sq_factor (n : ℕ+) : T ((n + 1) ^ 2) = T n * T (n + 1) :=
  by unfold T; apply pnat.eq; simp; ring



section results

variables {f : ℕ+ → S} (fmax : ∀ a b : ℕ+, f (a * b) = max (f a) (f b))
include fmax

private lemma lem1 {n : ℕ+} (h : ¬good f (n + 1)) (h0 : f (T n) ≤ f (T (n + 1))) :
  f (T (n + 1)) < f (T (n + 1 + 1)) :=
begin
  apply lt_of_not_le; intros h1,
  apply h; unfold good,
  change 4 with 2 * 2,
  repeat {rw [pow_mul, ← T, T_sq_factor, fmax] },
  rw [max_eq_right h0, max_eq_left h1]
end

private lemma lem2 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n)
  {C : ℕ+} (h0 : N < C) (h1 : f (T C) ≤ f (T (C + 1))) :
  ∀ k : ℕ+, f (T (C + 1)) < f (T (C + 1 + k)) :=
begin
  suffices : ∀ k : ℕ+, f (T (C + k)) < f (T (C + k + 1)) ∧ f (T (C + 1)) < f (T (C + 1 + k)),
    intros k; exact and.right (this k),
  intros k; induction k using pnat.strong_induction_on with k k_ih,
  rcases eq_or_ne k 1 with rfl | h2,
  split; exact lem1 fmax (h _ (lt_trans h0 (pnat.lt_add_right C 1))) h1,
  rcases pnat.exists_eq_succ_of_ne_one h2 with ⟨k₀, rfl⟩,
  rcases k_ih k₀ (pnat.lt_add_right k₀ 1) with ⟨h3, h4⟩,
  replace h3 : f (T (C + k₀ + 1)) < f (T (C + k₀ + 1 + 1)) :=
    lem1 fmax (h _ (lt_trans h0 (pnat.lt_add_right C (k₀ + 1)))) (le_of_lt h3),
  rw [← add_assoc, and_iff_right h3],
  apply lt_trans h4,
  rwa [add_right_comm, add_add_add_comm]
end

private lemma lem3 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n) {C : ℕ+} (h0 : N < C) :
  f (T (C + 1)) < f (T C) :=
begin
  apply lt_of_not_le; intros h1,
  have h2 := lem2 fmax h h0 h1 (C * (C + 1)),
  rw [← one_add_mul, add_comm 1 C, ← sq, T_sq_factor, fmax, max_eq_right h1] at h2,
  exact lt_irrefl _ h2
end

private lemma lem4 {N : ℕ+} (h : ∀ n : ℕ+, N < n → ¬good f n) {C : ℕ+} (h0 : N < C) :
  ∀ k : ℕ+, f (T (C + k)) < f (T C) :=
begin
  intros k; apply pnat.rec_on k; clear k,
  exact lem3 fmax h h0,
  intros k h1,
  refine lt_trans _ h1,
  rw ← add_assoc,
  exact lem3 fmax h (lt_trans h0 (pnat.lt_add_right C k))
end

private lemma lem5 (N : ℕ+) (h : ∀ n : ℕ+, N < n → ¬good f n) : false :=
begin
  replace h := lem4 fmax h (pnat.lt_add_right N 1) (N * (N + 1)),
  rw [← one_add_mul, add_comm, ← sq, T_sq_factor, fmax, lt_iff_not_le] at h,
  exact h (le_max_right (f (T N)) (f (T (N + 1))))
end
  
end results



/-- Final solution -/
theorem final_solution_general {f : ℕ+ → S} (fmax : ∀ a b : ℕ+, f (a * b) = max (f a) (f b)) :
  set.infinite (set_of (good f)) :=
begin
  apply set.infinite_of_not_bdd_above; rintros ⟨N, h⟩,
  simp only [upper_bounds, set.mem_set_of] at h,
  apply lem5 fmax N,
  intros n h0 h1,
  rw lt_iff_not_le at h0,
  exact h0 (h h1)
end

end IMO2013N3
end IMOSL
