import data.nat.basic data.set.basic

/-! # Characterization of functions f : ℕ → ℕ with f(f(n)) = f(n) + 1 for all n ∈ ℕ -/

open_locale classical

theorem fgood_self (f : ℕ → ℕ) : (∀ n : ℕ, f (f n) = (f n).succ) ↔
  ∃ N : ℕ, (∀ n : ℕ, N ≤ n → f n = n.succ) ∧ (∀ n : ℕ, N ≤ f n) :=
begin
  refine ⟨(λ h, _), (λ ⟨N, h, h0⟩ n, h (f n) (h0 n))⟩,
  have h0 : ∃ n, n ∈ set.range f := ⟨f 0, set.mem_range_self 0⟩,
  use nat.find h0; refine ⟨(λ n, _), (λ n, nat.find_min' h0 ⟨n, rfl⟩)⟩,
  apply nat.le_induction; clear n,
  obtain ⟨c, h1⟩ := nat.find_spec h0,
  rw [← h1, h],
  rintros n - h1,
  rw [← nat.succ_eq_add_one, ← h1, h]
end
