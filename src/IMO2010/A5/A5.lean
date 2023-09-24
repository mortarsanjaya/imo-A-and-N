import algebra.module.basic ring_theory.coprime.lemmas

/-! # IMO 2010 A5 -/

namespace IMOSL
namespace IMO2010A5

/- ### Extra lemmas -/

/-- General lemma on left-cancellation of `•` on abelian groups embedding to `ι → ℤ` -/
lemma succ_nsmul_left_cancel_of_embed_to_int_pi {G : Type*} [add_comm_group G]
  {ι : Type*} {ρ : G →+ ι → ℤ} (h : (ρ : G → ι → ℤ).injective)
  (n : ℕ) (x y : G) (h1 : (n + 1) • x = (n + 1) • y) : x = y :=
  h $ funext $ λ i, mul_left_cancel₀ (int.coe_nat_ne_zero_iff_pos.mpr n.succ_pos) $
    let h2 : (n + 1) • ρ x = (n + 1) • ρ y :=
      (ρ.map_nsmul x _).symm.trans $ h1.symm ▸ ρ.map_nsmul y _ in
    (nsmul_eq_mul _ _).symm.trans $ (congr_fun h2 i).trans $ nsmul_eq_mul (n + 1) _





/- ### Start of the problem -/

def good {G : Type*} [add_monoid G] (f : G → G) :=
  ∀ x y : G, f (2 • f x + y) = 3 • x + f (x + y)



lemma neg_is_good {G : Type*} [add_comm_group G] : good (has_neg.neg : G → G) :=
  λ x y, (neg_add' _ _).trans $ eq_add_neg_iff_add_eq.mpr $ (sub_add_add_cancel _ _ _).trans $
    (smul_neg 2 x).symm ▸ (neg_neg (2 • x)).symm ▸ (succ_nsmul' x 2).symm

lemma good_imp_hom {G : Type*} [add_comm_group G]
  (h : ∀ x y : G, 2 • x = 2 • y → x = y) (h0 : ∀ x y : G, 3 • x = 3 • y → x = y)
  {f : G → G} (h1 : good f) : ∃ φ : G →+ G, f = φ :=
suffices ∀ x y : G, f (x + y) = f x + f y, from ⟨add_monoid_hom.mk' f this, rfl⟩,
have h2 : ∀ x : G, f (2 • f x) = 3 • x + f x,
  from λ x, add_zero (2 • f x) ▸ (h1 x 0).trans
    (congr_arg (has_add.add _) (congr_arg f $ add_zero x)),
have h3 : f.injective := λ x y h3, h0 x y $
  (sub_eq_of_eq_add $ h2 x).symm.trans $ h3.symm ▸ sub_eq_of_eq_add (h2 y),
---- Finishing
λ x y, suffices f (2 • f (x + y)) = f (2 • f x + 2 • f y),
  from h _ _ $ h3 $ this.trans $ congr_arg f (nsmul_add _ _ _).symm,
(h2 _).trans $ (congr_arg2 _ (nsmul_add _ _ _) (congr_arg f $ add_comm x y)).trans $
  (add_assoc _ _ _).trans $ h1 y x ▸ add_comm x (2 • f y) ▸ (h1 _ _).symm

lemma hom_good_equality {G : Type*} [add_comm_group G] {φ : G →+ G} (h : good φ) (x : G) :
  2 • φ (φ x) = 3 • x + φ x :=
  (map_nsmul φ 2 _).symm.trans $ add_zero (2 • φ x) ▸
    (h _ 0).trans ((add_zero x).symm ▸ rfl)

lemma hom_good_eq_neg_of_embed_to_int_pi {G : Type*} [add_comm_group G]
  {ι : Type*} {ρ : G →+ ι → ℤ} (h : (ρ : G → ι → ℤ).injective)
  {f : G → G} (h0 : ∀ x, 2 • f (f x) = 3 • x + f x) :
  f = has_neg.neg :=
let γ : G → G := λ x, f x + x in suffices ∀ x, γ x = 0,
  from funext $ λ x, eq_neg_of_add_eq_zero_left (this x),
---- The main equation
have h0 : ∀ (x : G) (i : ι), 2 • ρ (γ (f x)) i = 3 • ρ (γ x) i :=
  λ x, suffices 2 • γ (f x) = 3 • γ x,
    from congr_fun $ (ρ.map_nsmul _ 2).symm.trans $ this.symm ▸ ρ.map_nsmul _ 3,
  (nsmul_add _ _ _).trans $ (h0 x).symm ▸ (nsmul_add (f x) x 3).symm ▸
    add_comm (3 • x) (3 • f x) ▸ (add_assoc _ _ _).trans
    (congr_arg2 _ rfl (succ_nsmul _ _).symm),
---- Reduce to `2 ^ k ∣ ρ (γ x) i` for all `i : ι`, `k : ℕ`, and `x : G`.
suffices ∀ (i : ι) (k : ℕ) (x : G), 2 ^ k ∣ ρ (γ x) i,
  from λ x, (map_eq_zero_iff ρ h).mp $ funext $ λ i,
    int.eq_zero_of_abs_lt_dvd (this i (ρ (γ x) i).nat_abs x) $
    (int.abs_eq_nat_abs _).trans_lt $ int.coe_nat_one ▸ int.coe_nat_bit0 1 ▸
    int.coe_nat_pow 2 (ρ (γ x) i).nat_abs ▸ int.coe_nat_lt.mpr (nat.lt_two_pow _),
---- Prove `2 ^ k ∣ ρ (γ x) i` for all `k : ℕ` using induction
λ i k, nat.rec_on k (λ x, one_dvd _) $ λ k h x, have h1 : is_coprime (2 : ℤ) 3 :=
  ⟨-1, 1, (congr_arg2 _ (neg_one_mul 2) (one_mul 3)).trans $ neg_add_cancel_left 2 1⟩,
h1.pow_left.dvd_of_dvd_mul_left $ nsmul_eq_mul 3 (ρ (γ x) i) ▸ h0 x i ▸
  (nsmul_eq_mul 2 $ ρ (γ (f x)) i).symm ▸ mul_dvd_mul (dvd_refl 2) (h _)





/-- Final solution, general version -/
theorem final_solution {G : Type*} [add_comm_group G]
  {ι : Type*} {ρ : G →+ ι → ℤ} (h : (ρ : G → ι → ℤ).injective) {f : G → G} :
  good f ↔ f = has_neg.neg :=
⟨λ h0, hom_good_eq_neg_of_embed_to_int_pi h $
  let h1 := succ_nsmul_left_cancel_of_embed_to_int_pi h in
  exists.elim (good_imp_hom (h1 1) (h1 2) h0) $
    λ φ h2, h2.symm ▸ hom_good_equality (h2 ▸ h0),
λ h, h.symm ▸ neg_is_good⟩

end IMO2010A5
end IMOSL
