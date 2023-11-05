import extra.general_ineq.two_sq_mul_le_add_sq data.nat.interval

/-!
# The (unweighted) AM-GM inequality over totally ordered commutative rings

We prove a version of (arbitrary variables) AM-GM inequality
  on totally ordered commutative rings.
More generally, we prove that AM-GM holds over totally ordered commutative
  semirings `R` such that `a^2 + b^2 ≥ 2ab` for any `a b : R`.
In particular, we prove the same result for canonically ordered semifields.
(Unfortunately, canonically ordered semirings are not found in `mathlib`.)
We prove both a `multiset` version and a `finset` version of the AM-GM inequality.
-/

namespace IMOSL
namespace extra

section multiset_prop

open multiset

variables {α : Type*}

/-- If `n ≤ |T|`, we can find `U ≤ T` with `|U| = n` -/
lemma exists_le_card_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U : multiset α, U ≤ T ∧ U.card = n :=
begin
  generalize_hyp h0 : T.card = m at h, revert h0 T,
  refine nat.le_induction (λ T h0, ⟨T, le_refl T, h0⟩) (λ k h0 h1 T h2, _) m h,
  rcases T.empty_or_exists_mem with rfl | ⟨a, h3⟩,
  exact absurd h2 k.succ_ne_zero.symm,
  rcases exists_cons_of_mem h3 with ⟨U, rfl⟩,
  rw [card_cons, add_left_inj] at h2,
  cases h1 h2 with V h4,
  exact ⟨V, h4.1.trans (U.le_cons_self a), h4.2⟩
end

/-- If `n ≤ |T|`, we can find `U` and `V` with `|U| = n` and `T = U + V` -/
lemma exists_card_eq_add_eq {n : ℕ} {T : multiset α} (h : n ≤ T.card) :
  ∃ U V : multiset α, U.card = n ∧ T = U + V :=
  exists.elim (exists_le_card_eq h) $ λ U h0,
    exists.elim (multiset.le_iff_exists_add.mp h0.1) $ λ V h1, ⟨U, V, h0.2, h1⟩

/-- If `|T| = m + n`, we can find `U` and `V` with `|U| = m`, `|V| = n`, and `T = U + V` -/
lemma exists_card_eq_add_eq' {m n : ℕ} {T : multiset α} (h : T.card = m + n) :
  ∃ U V : multiset α, (U.card = m ∧ V.card = n) ∧ T = U + V :=
  exists.elim (exists_card_eq_add_eq $ (m.le_add_right n).trans_eq h.symm) $
    λ U h0, exists.elim h0 $ λ V h0, ⟨U, V, ⟨h0.1, add_right_injective U.card $
      (U.card_add V).symm.trans $ h0.1.symm ▸ h0.2 ▸ h⟩, h0.2⟩

end multiset_prop





section general_framework

open multiset

variables {R : Type*} [linear_ordered_comm_semiring R]

private def AM_GM_nice (n : ℕ) (X : multiset R) := (n : R) ^ n * X.prod ≤ X.sum ^ n

private lemma AM_GM_seed (X : multiset R) (h : X.card = 1) : AM_GM_nice 1 X :=
  exists.elim (card_eq_one.mp h) $ λ a h0, h0.symm ▸ (pow_one _).ge.trans_eq'
    (by rw [nat.cast_one, pow_one, one_mul, prod_singleton, sum_singleton])

private lemma AM_GM_double (h : ∀ a b : R, 2 * a * b ≤ a ^ 2 + b ^ 2) (n : ℕ) (h0 : 0 < n)
  (h1 : ∀ X : multiset R, (∀ r : R, r ∈ X → 0 ≤ r) → X.card = n → AM_GM_nice n X)
  (X : multiset R) (h2 : ∀ r : R, r ∈ X → 0 ≤ r) (h3 : X.card = 2 * n) :
  AM_GM_nice (2 * n) X :=
begin
  rcases exists_card_eq_add_eq' (h3.trans $ two_mul n) with ⟨Y, Z, ⟨hYn, hZn⟩, rfl⟩,
  rw [AM_GM_nice, sum_add, pow_mul (Y.sum + Z.sum)],
  have hY : ∀ r : R, r ∈ Y → 0 ≤ r := λ r H, h2 r $ mem_add.mpr $ or.inl H,
  have hZ : ∀ r : R, r ∈ Z → 0 ≤ r := λ r H, h2 r $ mem_add.mpr $ or.inr H,
  have hYs := sum_nonneg hY,
  have two_nonneg := (zero_lt_two' R).le,

  refine (pow_le_pow_of_le_left
    (mul_nonneg (pow_nonneg two_nonneg 2) (mul_nonneg hYs (sum_nonneg hZ)))
    (general_two_sq_mul_le_add_sq h Y.sum Z.sum) n).trans' _,
  rw [mul_pow, ← pow_mul, nat.cast_mul, mul_pow, mul_assoc, nat.cast_two],
  refine mul_le_mul_of_nonneg_left _ (pow_nonneg two_nonneg _),
  rw [prod_add, nat.mul_comm, mul_pow, pow_mul, sq, mul_mul_mul_comm],
  exact mul_le_mul (h1 Y hY hYn) (h1 Z hZ hZn)
    (mul_nonneg (pow_nonneg n.cast_nonneg n) (prod_nonneg hZ)) (pow_nonneg hYs n)
end

private lemma AM_GM_reduce (n : ℕ)
  (h : ∀ X : multiset R, (∀ r : R, r ∈ X → 0 ≤ r) → X.card = n + 1 → AM_GM_nice (n + 1) X)
  (X : multiset R) (h0 : ∀ r : R, r ∈ X → 0 ≤ r) (h1 : X.card = n) :
  AM_GM_nice n X :=
begin
  rcases n.eq_zero_or_pos with rfl | h2,
  rw [AM_GM_nice, pow_zero, pow_zero, one_mul, card_eq_zero.mp h1, prod_zero],
  have H := sum_nonneg h0,
  cases H.eq_or_lt with h3 h3,

  ---- Case 1: `X.sum = 0`
  { have h4 := eq_replicate_card.mpr (all_zero_of_le_zero_le_of_sum_eq_zero h0 h3.symm),
    rw [AM_GM_nice, ← h3, h4, h1, prod_replicate, zero_pow h2, mul_zero] },

  ---- Case 2: `X.sum > 0`
  { replace h := h (X.sum ::ₘ X.map (has_mul.mul n))
      (λ r h3, (mem_cons.mp h3).elim (λ h4, H.trans_eq h4.symm)
        (λ h4, exists.elim (mem_map.mp h4) $ λ x h4, h4.2 ▸ mul_nonneg n.cast_nonneg (h0 x h4.1)))
      ((card_cons _ _).trans $ congr_arg nat.succ $ (X.card_map _).trans h1),
    rw [AM_GM_nice, sum_cons, sum_map_mul_left, map_id', ← one_add_mul,
        add_comm 1 (n : R), ← n.cast_succ, mul_pow] at h,
    replace h := le_of_mul_le_mul_left h (pow_pos (nat.cast_pos.mpr n.succ_pos) _),
    rw [prod_cons, pow_succ, prod_map_mul, map_id', map_const, prod_replicate, h1] at h,
    exact le_of_mul_le_mul_left h h3 }
end

private lemma AM_GM_nice_inductive (h : ∀ a b : R, 2 * a * b ≤ a ^ 2 + b ^ 2) :
  ∀ (n : ℕ) (X : multiset R), (∀ r : R, r ∈ X → 0 ≤ r) → X.card = n → AM_GM_nice n X :=
  nat.cauchy_induction_two_mul AM_GM_reduce 0 (λ X _, AM_GM_seed X) (AM_GM_double h)

lemma AM_GM_general (h : ∀ a b : R, 2 * a * b ≤ a ^ 2 + b ^ 2)
  (X : multiset R) (h0 : ∀ r : R, r ∈ X → 0 ≤ r) :
  (X.card : R) ^ X.card * X.prod ≤ X.sum ^ X.card :=
  AM_GM_nice_inductive h X.card X h0 rfl

end general_framework





section ring

variables {R : Type*} [linear_ordered_comm_ring R]

/-- `multiset` AM-GM inequality for totally ordered commutative rings -/
theorem AM_GM_ordered_ring_multiset {X : multiset R} (h : ∀ r : R, r ∈ X → 0 ≤ r) :
  (X.card : R) ^ X.card * X.prod ≤ X.sum ^ X.card :=
  AM_GM_general two_mul_le_add_sq X h

/-- `finset` AM-GM inequality for totally ordered commutative rings -/
theorem AM_GM_ordered_ring_finset
  {ι : Type*} {S : finset ι} (x : ι → R) (h : ∀ i : ι, i ∈ S → 0 ≤ x i) :
  (S.card : R) ^ S.card * S.prod x ≤ S.sum x ^ S.card :=
  S.card_def.symm ▸ S.val.card_map x ▸ AM_GM_ordered_ring_multiset
    (λ r h0, exists.elim (multiset.mem_map.mp h0) $ λ i h0, (h i h0.1).trans_eq h0.2)

end ring



section canonical_semifield

variables {F : Type*} [canonically_linear_ordered_semifield F]

private lemma canonical_two_mul_le_add_sq :
  ∀ a b : F, 2 * a * b ≤ a ^ 2 + b ^ 2 :=
suffices ∀ a b : F, a ≤ b → 2 * a * b ≤ a ^ 2 + b ^ 2,
  from λ a b, (le_total a b).elim (this a b)
    (λ h, (mul_right_comm _ _ _).trans_le $ (this b a h).trans_eq (add_comm _ _)),
λ a b h, exists.elim (exists_add_of_le h) $ λ c h, le_iff_exists_add.mpr
  ⟨c ^ 2, by rw [h, add_sq, ← add_assoc, ← add_assoc, sq, ← add_mul, ← two_mul, mul_add]⟩

/-- `multiset` AM-GM inequality for canonically (totally) ordered semifields, no division. -/
theorem AM_GM_canonical_semifield_multiset' (X : multiset F) :
  (X.card : F) ^ X.card * X.prod ≤ X.sum ^ X.card :=
  AM_GM_general canonical_two_mul_le_add_sq X (λ r _, zero_le r)

/-- `finset` AM-GM inequality for canonically (totally) ordered semifields, no division. -/
theorem AM_GM_canonical_semifield_finset' {ι : Type*} {S : finset ι} (x : ι → F) :
  (S.card : F) ^ S.card * S.prod x ≤ S.sum x ^ S.card :=
  S.card_def.symm ▸ S.val.card_map x ▸ AM_GM_canonical_semifield_multiset' _

end canonical_semifield

end extra
end IMOSL
