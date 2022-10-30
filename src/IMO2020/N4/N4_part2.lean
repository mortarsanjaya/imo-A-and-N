import IMO2020.N4.N4_basic

/-! # IMO 2020 N4, Generalized Version (Part 2) -/

namespace IMOSL
namespace IMO2020N4

open function

def balanced (p : ℕ) := ∀ a b : ℕ,
  a.coprime p → b.coprime p → a < b → ∃ i : ℕ, 0 < i ∧ (F p^[i]) a ≤ (F p^[i]) b



section general_results

variables {p : ℕ} (h : odd p)
include h

private lemma lem1 :
  balanced p ↔ ∀ x : ℕ, x.coprime p → 2 * S0 h x = p * order_two_mod_p h :=
begin
  sorry
end

/-- Generally, if -1 is a power of 2 mod p, then p is balanced -/
private lemma lem2 (h0 : ∃ c : ℕ, p ∣ 2 ^ c + 1) : balanced p :=
begin
  sorry
end

/-- Generally, if p is balanced, then the order of 2 mod p is even -/
private lemma lem3 (h0 : balanced p) : even (order_two_mod_p h) :=
begin
  sorry
end

end general_results



section prime_results

variables {p : ℕ} (h : odd p) (hp : p.prime)
include hp

/-- Final solution, part 2 -/
theorem final_solution_part2 : balanced p ↔ even (order_two_mod_p h) :=
begin
  sorry
end

theorem balanced_3_mod_8 (h0 : p % 8 = 3) : balanced p :=
begin
  sorry
end

theorem balanced_5_mod_8 (h0 : p % 8 = 5) : balanced p :=
begin
  sorry
end

theorem not_balanced_7_mod_8 (h0 : p % 8 = 7) : ¬balanced p :=
begin
  sorry
end

end prime_results



/-- Final solution, part 2, original version -/
theorem final_solution_part2_original : {p | odd p ∧ p.prime ∧ ¬balanced p} :=
begin
  sorry
end

end IMO2020N4
end IMOSL
