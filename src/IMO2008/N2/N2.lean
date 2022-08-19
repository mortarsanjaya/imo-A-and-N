import data.nat.parity number_theory.arithmetic_function data.zmod.basic

/-! # IMO 2008 N2 -/

open nat.arithmetic_function function

namespace IMOSL
namespace IMO2008N2

/- Final solution, part 1 -/
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

/- Final solution, part 2 -/
theorem final_solution_part2 {a b : ℕ} (h : ∀ k : ℕ, even (card_factors ((a + k) * (b + k)))) :
  a = b :=
begin
  wlog h0 : a ≤ b := le_total a b using [a b, b a],
  swap,
  rw eq_comm; refine this (λ k, _),
  rw mul_comm; exact h k,
  rw le_iff_exists_add at h0,
  rcases h0 with ⟨c, rfl⟩,
  by_contra h0,
  rw [self_eq_add_right, ← ne.def] at h0,
  suffices : ∀ k : ℕ, a.succ ≤ k → (even (card_factors k) ↔ even (card_factors (k + 1))),
  { have h1 : ∀ k : ℕ, a.succ ≤ k → (even (card_factors k) ↔ even (card_factors a.succ)) :=
    begin
      intros k,
      refine nat.le_induction (by refl) _ k,
      clear k; intros k h1 h2,
      rw [← this k h1, h2]
    end,
    rcases a.succ.exists_infinite_primes with ⟨p, h2, h3⟩,
    have h4 := h1 p h2,
    rw [card_factors_apply_prime h3, ← h1 (p ^ 2), card_factors_apply_prime_pow h3] at h4,
    simp only [false_iff, not_true, even_two, nat.not_even_one] at h4; exact h4,
    rw sq; exact le_trans h2 (nat.le_mul_self p) },
  intros k h1,
  rw [le_iff_exists_add, nat.succ_eq_add_one] at h1,
  rcases h1 with ⟨k, rfl⟩,
  replace h := h (a * (c - 1) + (1 + k) * c),
  have h1 : a + 1 + k ≠ 0 := ne_of_gt (by rw add_right_comm; exact (a + k).succ_pos),
  have h2 : a + 1 + k + 1 ≠ 0 := ne_of_gt (a + 1 + k).succ_pos,
  rw [add_comm a c, add_assoc, ← add_assoc a, ← mul_one_add, add_comm 1, nat.sub_add_cancel
        (by rwa [nat.succ_le_iff, zero_lt_iff]), ← add_mul, ← one_add_mul, ← add_assoc,
      add_comm 1, mul_mul_mul_comm, card_factors_mul (mul_ne_zero h1 h2) (mul_ne_zero h0 h0),
      nat.even_add, card_factors_mul h0 h0] at h,
  simp only [even_add_self, iff_true] at h,
  rwa [← nat.even_add, ← card_factors_mul h1 h2]
end

end IMO2008N2
end IMOSL
