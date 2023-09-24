import algebra.module.basic

/-! # IMO 2018 A1 -/

namespace IMOSL
namespace IMO2018A1

/-- General lemma on left-cancellation of `•` on abelian groups embedding to `ι → ℤ` -/
lemma zsmul_left_cancel_of_embed_to_int_pi {G : Type*} [add_group G]
  {ι : Type*} {ρ : G →+ ι → ℤ} (h : (ρ : G → ι → ℤ).injective)
  {n : ℤ} (h0 : n ≠ 0) {x y : G} (h1 : n • x = n • y) : x = y :=
  h $ funext $ λ i, mul_left_cancel₀ h0 $ let h2 : n • ρ x = n • ρ y :=
      (ρ.map_zsmul x _).symm.trans $ h1.symm ▸ ρ.map_zsmul y _ in
    (zsmul_eq_mul _ _).symm.trans $ (congr_fun h2 i).trans $ zsmul_eq_mul _ n

/-- Final solution -/
theorem final_solution {n : ℤ} (h : 1 < |n|) {G : Type*} [add_group G]
  {ι : Type*} {ρ : G →+ ι → ℤ} (h0 : (ρ : G → ι → ℤ).injective) {f : G → G} :
  (∀ x y : G, f (n • (x + f y)) = n • f x + f y) ↔ f = 0 :=
-- First reduce to `n^k ∣ ρ_{f(x)}(i)` for each `i : ι`, `k : ℕ`, and `x : G`
⟨λ h1, suffices ∀ (i : ι) (k : ℕ) (x : G), (n.nat_abs : ℤ) ^ k ∣ ρ (f x) i,
  from funext $ λ x, h0 $ suffices ρ (f x) = 0, from this.trans ρ.map_zero.symm,
  funext $ λ i, int.eq_zero_of_abs_lt_dvd (this i (ρ (f x) i).nat_abs x) $
    (int.abs_eq_nat_abs _).trans_lt $ int.coe_nat_pow n.nat_abs (ρ (f x) i).nat_abs ▸
    int.coe_nat_lt.mpr (nat.lt_pow_self (int.coe_nat_lt.mp $ h.trans_eq n.abs_eq_nat_abs) _),
-- Now reduce to the equation `n • f(-f(0) + f(x)) = f(x)` for all `x : G`
suffices ∀ x, n • f (-f 0 + f x) = f x,
  from λ i k, nat.rec_on k (λ x, one_dvd _) $ λ k h2 x, let y := -f 0 + f x in
    this x ▸ (ρ.map_zsmul (f y) n).symm ▸ (pi.smul_apply n (ρ (f y)) i).symm ▸
    (zsmul_eq_mul (ρ (f y) i) n).symm ▸ mul_dvd_mul (int.nat_abs_dvd.mpr $ dvd_refl n) (h2 y),
-- Now prove `n • f(f(x)) = f(x)` for all `x : G`
have h2 : (0 : G) = n • 0 := (zsmul_zero n).symm,
have h3 : f (-f 0) = 0 :=
  suffices n • f (-f 0) = 0, from zsmul_left_cancel_of_embed_to_int_pi h0
    (abs_pos.mp $ h.trans' int.one_pos) (this.trans h2),
  self_eq_add_left.mp $ (h1 (-f 0) 0).trans $ (neg_add_self (f 0)).symm ▸ h2 ▸ rfl,
have h4 : ∀ x : G, f (n • x) = n • f x,
  from λ x, add_zero (n • f x) ▸ h3 ▸ h1 x (-f 0) ▸ h3.symm ▸ (add_zero x).symm ▸ rfl,
λ x, (h4 _).symm.trans $ (h1 _ _).trans $ h3.symm ▸ h2 ▸ zero_add (f x),
-- `←` direction: straightforward
λ h1, h1.symm ▸ λ x y, ((add_zero _).trans (smul_zero n)).symm⟩

end IMO2018A1
end IMOSL
