import IMO2020.N5.N5_extra.good_map IMO2020.N5.N5_extra.strong_map.lemmas

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



namespace strong_map

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} [fact p.prime] (f : strong_map M p)

theorem zero_iff : f = 0 ↔ ∀ k : ℕ, k ≠ 0 → k ≤ p → f k = 0 :=
begin
  split,
  rintros rfl k - -; rw strong_map.zero_apply,
  intros h; ext x; rw strong_map.zero_apply,
  rcases eq_or_ne x 0 with rfl | hx,
  rw strong_map.map_zero,
  rw [pstrong_val f hx, h p (fact.out p.prime).ne_zero (le_refl p), smul_zero, zero_add],
  refine h _ _ (le_of_lt (nat.mod_lt _ (fact.out p.prime).pos)),
  rw [ne.def, ← nat.dvd_iff_mod_eq_zero],
  exact nat.not_dvd_ord_compl (fact.out p.prime) hx
end

theorem big_coprime_good_mod {n : ℕ} (h : p < n) (h0 : p.coprime n) (h1 : good n f)
  {x y : ℕ} (hx : ¬p ∣ x) (hy : ¬p ∣ y) (h2 : (x + y) % p = n % p) : f x = f y :=
begin
  have X : ∀ a b : ℕ, b % a ≠ 0 ↔ ¬a ∣ b := λ a b, by rw [ne.def, nat.dvd_iff_mod_eq_zero],
  have h3 : x % p < n := lt_trans (nat.mod_lt x (fact.out p.prime).pos) h,
  have h4 : (n - x % p) % p = y % p := nat.modeq.add_right_cancel' (x % p)
    (by rw [nat.modeq, nat.sub_add_cancel (le_of_lt h3), add_comm, nat.mod_add_mod, h2]),
  rw [pstrong_mod_p f hx, h1 _ (n - x % p) (by rwa X), pstrong_mod_p f hy, pstrong_mod_p f, h4],
  rwa [← X, h4, X],
  rwa [← zero_lt_iff, tsub_pos_iff_lt],
  rw [add_comm, nat.sub_add_cancel  (le_of_lt h3)]
end

end strong_map



section distinction

open strong_map

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ} (hp : p.prime)
variables {f : additive_map M} (hs : strong p f)
include hp hs

/-- If a `p`-strong map `f` is `n`-good for some `n > p` coprime with `p`, then `f = 0`. -/
theorem pstrong_big_coprime_is_zero {n : ℕ} (h : p < n) (h0 : p.coprime n) (h1 : good n f) :
  f = 0 :=
begin
  haveI : fact p.prime := ⟨hp⟩,
  lift f to strong_map M p using hs,
  rw coe_additive_map at h1,
  suffices : ∀ k : ℕ, k ≠ 0 → k < p → f k = 0,
  { change (0 : additive_map M) with ↑(0 : strong_map M p),
    rw [to_additive_map_inj, zero_iff]; intros k h2 h3,
    rw [le_iff_lt_or_eq, eq_comm] at h3; rcases h3 with h3 | rfl,
    exact this k h2 h3,
    rw h1 p (n - p) h2 (ne_of_gt (tsub_pos_of_lt h)) (nat.add_sub_of_le (le_of_lt h)),
    replace h0 : ¬p ∣ n - p := by rwa [nat.dvd_add_iff_left (dvd_refl p),
      nat.sub_add_cancel (le_of_lt h), ← hp.coprime_iff_not_dvd],
    rw pstrong_mod_p f h0; refine this _ _ (nat.mod_lt _ hp.pos),
    rwa [ne.def, ← nat.dvd_iff_mod_eq_zero] },
  intros k h2 h3,
  rcases eq_or_ne k (p - 1) with rfl | h4,
  rw [is_strong f 1 _ 1 h2 one_ne_zero, map_one_zero],
  rw [nat.sub_add_cancel (le_of_lt hp.one_lt), pow_one],

  ---- The main case: k < p - 1
  rw [ne.def, ← add_left_inj 1, nat.sub_add_cancel (le_of_lt hp.one_lt)] at h4,
  suffices : ∃ x : ℕ, (x * (k + 1)) % p = n % p,
  { cases this with x h6,
    have h5 : ¬p ∣ x :=
    begin
      rintros ⟨c, rfl⟩,
      rw [mul_assoc, nat.mul_mod_right, eq_comm, ← nat.dvd_iff_mod_eq_zero] at h6,
      rw hp.coprime_iff_not_dvd at h0; exact h0 h6
    end,
    rw mul_add_one at h6,
    replace h6 := strong_map.big_coprime_good_mod f h h0 h1 (hp.not_dvd_mul h5 _) h5 h6,
    rwa [map_mul_add f (λ h7, h5 ⟨0, by rw [mul_zero, h7]⟩ : x ≠ 0) h2, add_right_eq_self] at h6,
    exact nat.not_dvd_of_pos_of_lt (by rwa zero_lt_iff) h3 },
  rw [← nat.succ_le_iff, le_iff_eq_or_lt, or_iff_right h4, nat.succ_eq_add_one] at h3,
  replace h4 : ∃ y : ℕ, (k + 1) * y % p = 1 :=
  begin
    refine nat.exists_mul_mod_eq_one_of_coprime _ hp.one_lt,
    rw [nat.coprime_comm, hp.coprime_iff_not_dvd, nat.dvd_iff_mod_eq_zero,
        ← ne.def, ← zero_lt_iff, nat.mod_eq_of_lt h3],
    exact k.succ_pos
  end,
  cases h4 with y h4,
  use n * y; rw [mul_assoc, mul_comm y, nat.mul_mod, h4, mul_one, nat.mod_mod]
end

private lemma pstrong_qgood_is_zero {q : ℕ} (hq : q.prime) (h : p < q) (h0 : good q f) : f = 0 :=
begin
  refine pstrong_big_coprime_is_zero hp hs h _ h0,
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
