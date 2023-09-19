import data.fintype.card data.set.finite

/-! # IMO 2017 A3 -/

namespace IMOSL
namespace IMO2017A3

section finite_npow

variables {M : Type*} [has_pow M ℕ] [fintype M] (x : M)

lemma npow_not_inj_of_finite : ∃ a b : ℕ, a ≠ b ∧ x ^ a = x ^ b := 
  finite.exists_ne_map_eq_of_infinite _

lemma npow_not_inj_of_finite2 : ∃ a b : ℕ, a < b ∧ x ^ a = x ^ b :=
  exists.elim (npow_not_inj_of_finite x) $ λ a h, exists.elim h $ λ b h0,
    (lt_or_gt_of_ne h0.1).elim (λ h1, ⟨a, b, h1, h0.2⟩) (λ h1, ⟨b, a, h1, h0.2.symm⟩)

lemma npow_not_inj_of_finite3 : ∃ n k : ℕ, 0 < k ∧ x ^ (n + k) = x ^ n :=
  exists.elim (npow_not_inj_of_finite2 x) $ λ a h, exists.elim h $ λ b h0,
    ⟨a, b - a, nat.sub_pos_of_lt h0.1, (nat.add_sub_of_le h0.1.le).symm ▸ h0.2.symm⟩

end finite_npow


section monoid_npow

variables {M : Type*} [monoid M] {x : M} {n k : ℕ} (h : x ^ (n + k) = x ^ n)
include h

lemma npow_mul_add_eq_of_npow_add_eq : ∀ t : ℕ, x ^ (n + t * k) = x ^ n
| 0 := k.zero_mul.symm ▸ n.add_zero.symm ▸ rfl
| (t+1) := (add_one_mul t k).symm ▸ n.add_assoc (t * k) k ▸ (pow_add _ _ _).trans
    ((npow_mul_add_eq_of_npow_add_eq t).symm ▸ (pow_add x n k).symm.trans h) 

lemma npow_add_eq_of_npow_add_eq_of_le {n0 : ℕ} (h0 : n ≤ n0) : x ^ (n0 + k) = x ^ n0 :=
  exists.elim (le_iff_exists_add'.mp h0) $ λ c h0, h0.symm ▸
    (c.add_assoc n k).symm ▸ (pow_add x c n).symm ▸ h ▸ pow_add x c _ 
end monoid_npow





/-- Final solution, monoid version (the claim) -/
theorem final_solution_monoid {M : Type*} [monoid M] [fintype M]
  {x : M} (h : ∀ y : M, x * y * x = y * x * y → y = x) :
  ∃ m : ℕ, 1 < m ∧ x ^ m = x :=
---- Take some `k > 0` and `n ≥ 0` such that `x^{n + k} = x^n`
exists.elim (npow_not_inj_of_finite3 x) $
  λ n h0, exists.elim h0 $ λ k h0, n.eq_zero_or_pos.elim
---- Case `n = 0`
(λ h1, ⟨k + 1, nat.succ_lt_succ h0.1,
    suffices x ^ k = 1, from (pow_succ x k).trans $ this.symm ▸ mul_one x,
    pow_zero x ▸ k.zero_add ▸ h1 ▸ h0.2⟩) $
---- Case `n ≠ 0` 
λ h1, let d := n * k in ⟨d + 1, nat.succ_lt_succ (nat.mul_pos h1 h0.1), h _ $
have h : x ^ (d + d) = x ^ d := npow_add_eq_of_npow_add_eq_of_le
  (npow_mul_add_eq_of_npow_add_eq h0.2 n) (nat.le_mul_of_pos_right h0.1),
by rw [mul_assoc, pow_mul_comm', mul_assoc, ← pow_succ, ← pow_add,
  add_add_add_comm, pow_add x (d + d), h, ← pow_add]⟩

/-- Final solution -/
theorem final_solution {S : Type*} [fintype S] [decidable_eq S]
  {f : function.End S} (h : ∀ g : S → S, f * g * f = g * f * g → g = f) :
  set.range (f ∘ f) = set.range f :=
  (set.range_comp_subset_range f f).antisymm $ exists.elim (final_solution_monoid h) $
    λ m h, (congr_arg _ h.2.symm).trans_subset $
      exists.elim (le_iff_exists_add.mp $ nat.succ_le_iff.mpr h.1) $
      λ c h, h.symm ▸ (pow_add f 2 c).symm ▸ set.range_comp_subset_range _ (f ∘ f)

end IMO2017A3
end IMOSL
