import data.nat.parity number_theory.arithmetic_function data.zmod.basic

/-! # IMO 2008 N2 -/

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
  refine ⟨a, b, h0, (λ n h1, _)⟩,
  replace h := congr_fun h ⟨n, h1⟩,
  dsimp only [f] at h,
  rw [fin.coe_mk, zmod.nat_coe_eq_nat_coe_iff'] at h,
  cases eq_or_ne (a + n) 0 with h2 h2,
  rw [h2, zero_mul, nat.arithmetic_function.map_zero]; exact even_zero,
  cases eq_or_ne (b + n) 0 with h3 h3,
  rw [h3, mul_zero, nat.arithmetic_function.map_zero]; exact even_zero,
  rw [card_factors_mul h2 h3, nat.even_add, nat.even_iff, nat.even_iff, h]
end

private lemma lem1 {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
  even (card_factors (u * v)) ↔ (even (card_factors u) ↔ even (card_factors v)) :=
  by rw [card_factors_mul (ne_of_gt hu) (ne_of_gt hv), nat.even_add]

/-- Final solution, part 2 -/
theorem final_solution_part2 {a b : ℕ} (h : ∀ k : ℕ, even (card_factors ((a + k) * (b + k)))) :
  a = b :=
begin
  wlog h0 : a ≤ b := le_total a b using [a b, b a],
  work_on_goal 2 { rw this (λ k, by rw mul_comm; exact h k) },
  rw le_iff_exists_add at h0; rcases h0 with ⟨c, rfl⟩,
  by_contra h0,
  rw [self_eq_add_right, ← ne.def, ← zero_lt_iff] at h0,
  replace h : ∀ k : ℕ, a ≤ k → (even (card_factors k) ↔ even (card_factors a)) :=
  begin
    suffices : ∀ k : ℕ, a ≤ k → (even (card_factors k) ↔ even (card_factors (k + 1))),
    { refine (λ k, nat.le_induction (by refl) _ k),
      intros n h1 h2; rw [← this n h1, h2] },
    intros k h1,
    rcases k.eq_zero_or_pos with rfl | h2,
    rw [nat.arithmetic_function.map_zero, zero_add, card_factors_one],
    replace h1 : a ≤ k * c := le_trans h1 ((le_mul_iff_one_le_right h2).mpr h0),
    rw le_iff_exists_add at h1; cases h1 with m h1,
    replace h := h m,
    rw [add_right_comm, ← h1, ← add_one_mul, mul_mul_mul_comm,
        lem1 (mul_pos h2 k.succ_pos) (mul_pos h0 h0), lem1 h2 k.succ_pos] at h,
    rw [h, card_factors_mul (ne_of_gt h0) (ne_of_gt h0)]; exact even_add_self _
  end,
  rcases a.exists_infinite_primes with ⟨p, h1, h2⟩,
  replace h0 := h p h1,
  rw [card_factors_apply_prime h2, ← h (p ^ 2), card_factors_apply_prime_pow h2] at h0,
  simp only [false_iff, not_true, even_two, nat.not_even_one] at h0; exact h0,
  rw sq; exact le_trans h1 (nat.le_mul_self p)
end

end IMO2008N2
end IMOSL
