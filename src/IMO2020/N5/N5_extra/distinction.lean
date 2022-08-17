import IMO2020.N5.N5_extra.good_map

/-!
# Distinction between wide and `p`-strong additive maps

Let `f` be a `p`-strong additive map, where `p` is a prime.
We prove that `f` is zero if one of the following holds:
* `f` is `n`-good for some `n > p` coprime with `p`,
* `f` is wide,
* `f` is `q`-strong for some prime `q ≠ p`.
-/

namespace IMOSL
namespace IMO2020N5



section distinction

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} (hp : p.prime)
variables {f : additive_map M} (hs : strong p f)
include hp hs

/-- If a `p`-strong map `f` is `n`-good for some `n > p` coprime with `p`, then `f = 0`. -/
theorem pstrong_and_big_coprime_good_is_zero
  {n : ℕ} (h : p < n) (h0 : p.coprime n) (h1 : good n f) : f = 0 :=
begin
  sorry
end

private lemma pstrong_qgood_is_zero {q : ℕ} (hq : q.prime) (h : p < q) (h0 : good q f) : f = 0 :=
begin
  refine pstrong_and_big_coprime_good_is_zero hp hs h _ h0,
  rw nat.coprime_primes hp hq; exact ne_of_lt h
end

/-- If a `p`-strong map `f` is wide, then `f = 0`. -/
theorem pstrong_wide_is_zero (h : wide f) : f = 0 :=
begin
  rcases h.exists_nat_lt p with ⟨q, ⟨hq, h0⟩, h1⟩,
  exact pstrong_qgood_is_zero hp hs hq h1 h0
end

/-- If a `p`-strong map `f` is `q`-strong for some prime `q ≠ p`, then `f = 0`. -/
theorem pstrong_qstrong_is_zero {q : ℕ} (hq : q.prime) (h : p ≠ q) (h0 : strong q f) : f = 0 :=
begin
  wlog h1 : p < q := lt_or_gt_of_ne h using [p q, q p],
  replace h0 := h0 1,
  rw pow_one at h0,
  exact pstrong_qgood_is_zero hp hs hq h1 h0
end






end distinction

end IMO2020N5
end IMOSL
