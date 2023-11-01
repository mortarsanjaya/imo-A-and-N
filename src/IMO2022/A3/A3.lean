import algebra.order.positive.ring algebra.group_power.order

/-! # IMO 2022 A3 (P2), Ring Version -/

namespace IMOSL
namespace IMO2022A3

variables {R : Type*} [linear_ordered_comm_ring R]

/-! ## Extra lemmas -/

lemma two_mul_le_add_sq (x y : {x : R // 0 < x}) : 2 * x * y ≤ x ^ 2 + y ^ 2 :=
  two_mul_le_add_sq x y

lemma exists_add_of_lt {x y : {x : R // 0 < x}} (h : x < y) :
  ∃ c : {x : R // 0 < x}, x + c = y :=
  ⟨⟨y - x, sub_pos_of_lt h⟩, subtype.coe_injective $ add_sub_cancel'_right x y⟩

lemma add_sq (x y : {x : R // 0 < x}) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 :=
  subtype.coe_injective $ add_sq x.1 y.1

lemma lt_add_self (x y : {x : R // 0 < x}) : x < x + y :=
  lt_add_of_pos_right _ y.2

lemma strict_AM_GM {x y : {x : R // 0 < x}} (h : x < y) : 2 * x * y < x ^ 2 + y ^ 2 :=
  exists.elim (exists_add_of_lt h) $ λ c h,
    by rw [← h, add_sq, sq, ← add_assoc, ← add_assoc, ← two_mul, ← mul_assoc, ← mul_add];
    exact lt_add_self _ _

lemma AM_GM_le_case {x y : {x : R // 0 < x}} (h : x ^ 2 + y ^ 2 ≤ 2 * x * y) : x = y :=
  ((lt_trichotomy x y).resolve_left (λ h0, h.not_lt $ strict_AM_GM h0)).resolve_right $
    λ h0, h.not_lt $ (mul_right_comm 2 x y).trans_lt $ (strict_AM_GM h0).trans_eq $ add_comm _ _





/-! ## Start of the problem -/

def good (f : {x : R // 0 < x} → {x : R // 0 < x}) :=
  ∀ x : {x : R // 0 < x}, ∃! y : {x : R // 0 < x}, x * f y + y * f x ≤ 2

def good_alt (f : {x : R // 0 < x} → {x : R // 0 < x}) :=
  (∀ x : {x : R // 0 < x}, x * f x ≤ 1) ∧
    (∀ x y : {x : R // 0 < x}, x * f y + y * f x ≤ 2 → x = y) 



lemma inv_is_good {f : {x : R // 0 < x} → {x : R // 0 < x}} (h : ∀ x, x * f x = 1) : good f :=
λ x, ⟨x, let h := (h x).le in add_le_add h h, λ y h0, eq.symm $ AM_GM_le_case $
  (mul_assoc 2 x y).ge.trans' $ (mul_le_mul_right' h0 _).trans_eq' $
  (add_mul (x * f y) (y * f x) (x * y)).symm ▸ congr_arg2 _
    (mul_mul_mul_comm x x (f y) y ▸ mul_comm y (f y) ▸ sq x ▸ (h y).symm ▸ (mul_one _).symm)
    (mul_comm (f x) y ▸ mul_mul_mul_comm (f x) x y y ▸
      mul_comm x (f x) ▸ sq y ▸ (h x).symm ▸ (one_mul _).symm)⟩

lemma good_imp_good_alt {f : {x : R // 0 < x} → {x : R // 0 < x}} (h : good f) : good_alt f :=
suffices ∀ x : {x : R // 0 < x}, x * f x ≤ 1,
  from ⟨this, λ x y h0, (h x).unique (let h1 := this x in add_le_add h1 h1) h0⟩,
λ x, le_of_not_lt $ λ h0, exists.elim (h x).exists $ λ y h1, h1.not_lt $
  ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left (x * y) _ _ $
  (mul_rotate _ _ _).symm.trans_lt $ (two_mul_le_add_sq x y).trans_lt $
  (mul_add _ _ _).ge.trans_lt' $ add_lt_add
    (mul_mul_mul_comm x x y (f y) ▸ sq x ▸ lt_mul_of_one_lt_right' (x ^ 2)
      (lt_of_not_le $ λ h2, h0.not_le $ suffices y = x, from this ▸ h2,
        (h y).unique (add_le_add h2 h2) ((add_comm _ _).trans_le h1)))
    (mul_comm y x ▸ mul_mul_mul_comm y y x (f x) ▸ sq y ▸ lt_mul_of_one_lt_right' (y ^ 2) h0)

lemma good_alt_imp_eq_inv {f : {x : R // 0 < x} → {x : R // 0 < x}}
  (h : good_alt f) (x) : x * f x = 1 :=
(h.1 x).eq_or_lt.resolve_right $ λ h0, exists.elim (exists_add_of_lt h0) $
  λ M h1, have x < (1 + M) * x := lt_mul_of_one_lt_left' x (lt_add_self _ _),
  this.ne $ h.2 x ((1 + M) * x) $ add_le_add
    ((h.1 $ (1 + M) * x).trans' $ mul_le_mul_right' this.le _)
    ((mul_assoc _ _ _).trans_le $ (one_add_mul M _).trans_le $ h1.le.trans' $
      add_le_add_left (mul_le_of_le_one_right' h0.le) _)





/-- Final solution -/
theorem final_solution {f : {x : R // 0 < x} → {x : R // 0 < x}} :
  good f ↔ ∀ x, x * f x = 1 :=
⟨λ h, good_alt_imp_eq_inv (good_imp_good_alt h), inv_is_good⟩

end IMO2022A3
end IMOSL
