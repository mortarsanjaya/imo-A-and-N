import data.nat.parity number_theory.arithmetic_function data.zmod.basic

/-! # IMO 2009 N2 -/

namespace IMOSL
namespace IMO2008N2

open nat.arithmetic_function function

/-- Final solution, part 1 -/
theorem final_solution_part1 (N : ℕ) :
  ∃ a b : ℕ, a ≠ b ∧ (∀ k : ℕ, k < N → even (card_factors ((a + k) * (b + k)))) :=
begin
  let f : ℕ → (fin N) → (zmod 2) := λ (a : ℕ) (k : fin N), card_factors (a + k),
  have h : ¬injective f := not_injective_infinite_finite f,
  simp only [injective, not_forall] at h,
  rcases h with ⟨a, b, h, h0⟩,
  refine ⟨a, b, h0, λ n h1, _⟩,
  replace h := congr_fun h ⟨n, h1⟩,
  dsimp only [f] at h; clear f,
  rw [fin.coe_mk, zmod.nat_coe_eq_nat_coe_iff'] at h,
  cases eq_or_ne (a + n) 0 with h2 h2,
  rw [h2, zero_mul, nat.arithmetic_function.map_zero]; exact even_zero,
  cases eq_or_ne (b + n) 0 with h3 h3,
  rw [h3, mul_zero, nat.arithmetic_function.map_zero]; exact even_zero,
  rw [card_factors_mul h2 h3, nat.even_add, nat.even_iff, nat.even_iff, h]
end



/-- Final solution, part 2 -/
theorem final_solution_part2 :
  ∀ {a b : ℕ}, (∀ k : ℕ, even (card_factors ((a + k) * (b + k)))) → a = b :=
begin
  ---- Use suffices since WLOG seems to be a bit slow
  suffices : ∀ {a b : ℕ}, (∀ k : ℕ, even (card_factors ((a + k) * (b + k)))) → a ≤ b → a = b,
  { intros a b h,
    cases le_total a b with h0 h0,
    exact this h h0,
    refine (this (λ k, _) h0).symm,
    rw mul_comm; exact h k },
  intros a b h h0,
  rw le_iff_exists_add at h0; rcases h0 with ⟨c, rfl⟩,
  by_contra h0; rw [self_eq_add_right, ← ne.def, ← zero_lt_iff] at h0,

  ---- Reduce to `Ω(k) ≡ Ω(k + 1) (mod 2)` for all `k ≥ a`
  suffices : ∀ k : ℕ, a ≤ k → (even (card_factors k) ↔ even (card_factors a)),
  { rcases a.exists_infinite_primes with ⟨p, h1, h2⟩,
    replace h0 := this p h1,
    rw [card_factors_apply_prime h2, ← this (p ^ 2), card_factors_apply_prime_pow h2] at h0,
    simp only [false_iff, not_true, even_two, nat.not_even_one] at h0; exact h0,
    rw sq; exact le_trans h1 (nat.le_mul_self p) },
  suffices : ∀ k : ℕ, a ≤ k → (even (card_factors k) ↔ even (card_factors (k + 1))),
  { refine (λ k, nat.le_induction (by refl) _ k),
    intros n h1 h2; rw [← this n h1, h2] },

  ---- Finishing
  intros k h1,
  rcases k.eq_zero_or_pos with rfl | h2,
  rw [nat.arithmetic_function.map_zero, zero_add, card_factors_one],
  replace h1 : a ≤ k * c := le_trans h1 ((le_mul_iff_one_le_right h2).mpr h0),
  rw le_iff_exists_add at h1; cases h1 with m h1,
  replace h := h m,
  rw zero_lt_iff at h0 h2,
  rw [add_right_comm, ← h1, ← add_one_mul, mul_mul_mul_comm, card_factors_mul,
      nat.even_add, card_factors_mul h2 k.succ_ne_zero, nat.even_add] at h,
  rw [h, card_factors_mul h0 h0, nat.even_add],
  exacts [mul_ne_zero h2 k.succ_ne_zero, mul_ne_zero h0 h0]
end

end IMO2008N2
end IMOSL
