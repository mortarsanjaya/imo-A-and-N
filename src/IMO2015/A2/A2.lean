import data.int.order.basic

/-! # IMO 2015 A2 -/

namespace IMOSL
namespace IMO2015A2

def good (f : ℤ → ℤ) := ∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1





lemma add_one_is_good : good (λ x : ℤ, x + 1) :=
  λ x y, eq.symm $ (sub_sub _ _ _).trans $
    (add_sub_add_right_eq_sub _ _ _).trans $ add_sub_right_comm _ _ _

lemma const_neg_one_is_good : good (λ _ : ℤ, -1) :=
  λ _ _, (sub_eq_neg_self.mpr $ sub_self (-1)).symm



section lemmas

variables {f : ℤ → ℤ} (h : good f)
include h

lemma map_map_eq_map_add_one (x : ℤ) : f (x + 1) = f (f x) :=
  let A := 0 - f (f 0), h0 : f A = -1 := (h 0 (f 0)).trans $ sub_eq_neg_self.mpr (sub_self _) in
    (congr_arg f $ (congr_arg2 _ rfl h0).trans $ sub_neg_eq_add x 1).symm.trans $
      (h x A).trans $ sub_eq_of_eq_add $ h0.symm ▸ sub_neg_eq_add _ _

lemma map_is_linear : ∀ x : ℤ, f x = f 0 + (f (-1) + 1) * x :=
let A := f (-1) + 1 in suffices ∀ x, f (x + 1) = f x + A,
  from λ x, int.induction_on' x 0 (A.mul_zero.symm ▸ (f 0).add_zero.symm)
    (λ k _ h0, (this k).trans $ h0.symm ▸
      (mul_add_one A k).symm ▸ int.add_assoc _ _ _)
    (λ k _ h0, (sub_eq_of_eq_add $ this (k - 1)).symm.trans $ (mul_sub_one A k).symm ▸
      (sub_add_cancel k 1).symm ▸ h0.symm ▸ add_sub_assoc _ _ _),
λ x, let h0 := map_map_eq_map_add_one h in suffices f (x - f x) = f (-1),
  from (h0 x).trans $ eq_add_of_sub_eq' $ eq_add_of_sub_eq $ (h x x).symm.trans this,
suffices f (x - f x - 1) = -1, from sub_add_cancel (x - f x) 1 ▸ congr_arg f this ▸ h0 _,
  (congr_arg f $ sub_right_comm x 1 (f x)).symm.trans $ (h _ x).trans $ sub_eq_neg_self.mpr $
    sub_eq_zero_of_eq $ (h0 _).symm.trans $ congr_arg f $ sub_add_cancel x 1

end lemmas





/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} : good f ↔ f = (λ _, -1) ∨ f = (λ x : ℤ, x + 1) :=
⟨λ h, let h0 := map_is_linear h in (eq_or_ne (f (-1) + 1) 0).imp
  ---- Case 1: `f(-1) + 1 = 0`, thus `f` is constant
  (λ h1, suffices ∀ x, f x = f 0,
    from funext $ λ x, (this x).trans $ (this (-1)).symm.trans $ eq_neg_of_add_eq_zero_left h1,
  λ x, (h0 x).trans $ add_right_eq_self.mpr $ mul_eq_zero_of_left h1 x)
  ---- Case 2: `f(-1) + 1 ≠ 0`, thus `f` is injective
  (λ h1, suffices function.injective f,
    from funext $ λ x, this (map_map_eq_map_add_one h x).symm,
  λ a b h, mul_right_injective₀ h1 $ add_right_injective (f 0) $
    (h0 a).symm.trans $ h.trans $ h0 b),
λ h, h.elim (λ h, h.symm ▸ const_neg_one_is_good) (λ h, h.symm ▸ add_one_is_good)⟩

end IMO2015A2
end IMOSL
