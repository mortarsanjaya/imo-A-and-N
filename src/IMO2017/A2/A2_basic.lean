import algebra.ring.defs data.finset.pointwise

/-! # IMO 2017 A2, Basic File -/

namespace IMOSL
namespace IMO2017A2

open finset
open_locale pointwise

variables {R : Type*} [ring R]

def is_sq_add_diff (T : finset R) (x : R) :=
  ∃ a b c d : R, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T ∧ x = (a ^ 2 + b ^ 2) - (c ^ 2 + d ^ 2)

def good (q : R) (T : finset R) :=
  ∀ u v : R, u ∈ T → v ∈ T → is_sq_add_diff T (q * (u * v))

def excellent [decidable_eq R] (k : ℕ) (q : R) :=
  ∀ T : finset R, T.card = k → good q (T - T)



lemma sq_add_diff_is_sq_add_diff {T : finset R} {a b c d : R}
  (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) (hd : d ∈ T) :
  is_sq_add_diff T ((a ^ 2 + b ^ 2) - (c ^ 2 + d ^ 2)) :=
  ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩

lemma zero_is_sq_add_diff_of_mem {T : finset R} {r : R}
  (h : r ∈ T) : is_sq_add_diff T (0 : R) :=
  ⟨r, r, r, r, h, h, h, h, (sub_self (r ^ 2 + r ^ 2)).symm⟩

lemma good_zero_any (T : finset R) : good 0 T :=
  λ u v h h0, (zero_mul (u * v)).symm ▸ zero_is_sq_add_diff_of_mem h

lemma excellent_any_zero [decidable_eq R] (k : ℕ) : excellent k (0 : R) :=
  λ T _, good_zero_any (T - T)

lemma neg_is_sq_add_diff {T : finset R} {x : R}
  (h : is_sq_add_diff T x) : is_sq_add_diff T (-x) :=
  exists.elim h $ λ a h, exists.elim h $ λ b h,
    exists.elim h $ λ c h, exists.elim h $ λ d h,
      ⟨c, d, a, b, h.2.2.1, h.2.2.2.1, h.1, h.2.1,
        neg_eq_iff_eq_neg.mpr $ h.2.2.2.2.trans (neg_sub _ _).symm⟩

lemma good_neg_of_good {q : R} {T : finset R} (h : good q T) : good (-q) T :=
  λ u v h0 h1, (neg_mul q (u * v)).symm ▸ neg_is_sq_add_diff (h u v h0 h1)

lemma excellent_neg_of_excellent [decidable_eq R]
  {k : ℕ} {q : R} (h : excellent k q) : excellent k (-q) :=
  λ T h0, good_neg_of_good (h T h0)

lemma is_sq_add_diff_of_good_one_mem {q : R} {T : finset R}
  (h : good q T) (h0 : (1 : R) ∈ T) : is_sq_add_diff T q :=
  mul_one q ▸ mul_one (1 : R) ▸ h 1 1 h0 h0

end IMO2017A2
end IMOSL
