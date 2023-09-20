import algebra.group_power.lemmas tactic.ring

/-! # IMO 2017 A6 (P2) -/

namespace IMOSL
namespace IMO2017A6

open function

def good {R : Type*} [ring R] (f : R → R) :=
  ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y)





/- ### Answer checking -/

lemma good_zero {R : Type*} [ring R] : good (0 : R → R) :=
  λ _ _, add_zero 0
  
lemma good_one_sub {R : Type*} [comm_ring R] : good (has_sub.sub (1 : R)) :=
  λ x y, by ring





/- ### The solution -/

section ring

variables {R : Type*} [ring R] {f : R → R} (h : good f)
include h

lemma good_neg : good (-f) :=
  λ x y, (neg_add _ _).symm.trans $ congr_arg has_neg.neg $
    (neg_mul_neg (f x) (f y)).symm ▸ h x y

/-- (1) -/
lemma good_special_equality {x y : R} (h0 : x * y = 1) :
  f (f (x + 1) * f (y + 1)) = 0 :=
  add_left_eq_self.mp $ (h _ _).trans $ congr_arg f $ (add_one_mul x _).trans $
    congr_arg (+ (y + 1)) $ (mul_add_one x y).trans $ (congr_arg (+ x) h0).trans $
    add_comm 1 x

lemma good_map_map_zero_sq : f (f 0 ^ 2) = 0 :=
  (congr_arg f $ sq $ f 0).trans $ add_left_eq_self.mp $ (h 0 0).trans $
    congr_arg f $ (mul_zero 0).trans (add_zero 0).symm

lemma good_eq_of_inj (h0 : f 0 = 1) (h1 : injective f) : f = has_sub.sub 1 :=
---- Reduce to `∀ x : R, f (f x) + f x = 1`
suffices ∀ x : R, f (f x) + f x = 1,
  from funext $ λ x, (eq_sub_of_add_eq' $ this x).trans $ congr_arg2 _ rfl $
    h1 $ (eq_sub_of_add_eq $ this (f x)).trans (eq_sub_of_add_eq' $ this x).symm,
---- Prove `∀ x : R, f (f x) + f x = 1`
λ x, let h : f (f x * 1) + f (x + 0) = f (x * 0) := h0 ▸ h x 0 in
  (congr_arg2 (λ u v, f u + f v) (mul_one (f x)).symm (add_zero x).symm).trans $
    h.trans $ (mul_zero x).symm ▸ h0

end ring



section division_ring

variables {R : Type*} [division_ring R] {f : R → R} (h : good f)
include h

lemma good_map_eq_zero (h0 : f ≠ 0) {c : R} (h1 : f c = 0) : c = 1 :=
---- Reduce to `f(0) = 0`
h0.imp_symm $ λ h2, suffices f 0 = 0, from funext $ λ x,
  (add_left_eq_self.mpr this).symm.trans $ (congr_arg2 (λ u v, f u + f v)
    (mul_eq_zero_of_right (f x) this).symm (add_zero x).symm).trans $
    (h x 0).trans $ (mul_zero x).symm ▸ this,
---- Prove `f(0) = 0`
let h3 : f (c - 1 + 1) = 0 := (sub_add_cancel c 1).symm ▸ h1 in
  (congr_arg f $ mul_eq_zero_of_left h3 _).symm.trans $
    good_special_equality h (mul_inv_cancel $ sub_ne_zero_of_ne h2)

lemma good_map_zero_sq (h0 : f ≠ 0) : f 0 ^ 2 = 1 :=
  good_map_eq_zero h h0 (good_map_map_zero_sq h)

lemma good_map_zero (h0 : f ≠ 0) : f 0 = 1 ∨ f 0 = -1 :=
  sq_eq_one_iff.mp (good_map_zero_sq h h0)

lemma good_map_one : f 1 = 0 :=
  (eq_or_ne f 0).elim (λ h0, congr_fun h0 1)
    (λ h0, good_map_zero_sq h h0 ▸ good_map_map_zero_sq h)

/-- (2) -/
lemma good_map_eq_zero_iff (h0 : f 0 = 1) (c : R) : f c = 0 ↔ c = 1 :=
  ⟨good_map_eq_zero h $ λ h1, absurd ((congr_fun h1 0).symm.trans h0) zero_ne_one,
  λ h1, (congr_arg f h1).trans (good_map_one h)⟩

/-- (3) -/
lemma good_shift (h0 : f 0 = 1) (x : R) : f (x + 1) + 1 = f x :=
  (add_comm _ _).trans $ (congr_arg (+ f (x + 1)) $ h0.symm.trans $
    congr_arg f (mul_eq_zero_of_right (f x) (good_map_one h)).symm).trans $
    (h x 1).trans $ congr_arg f (mul_one x)

lemma good_shift2 (h0 : f 0 = 1) (x : R) : f (x - 1) = f x + 1 :=
  (good_shift h h0 _).symm.trans $ congr_arg (λ x, f x + 1) (sub_add_cancel x 1)

lemma good_map_add_one_inv (h0 : f ≠ 0) (x : R) : f (x⁻¹ + 1) = (f (x + 1))⁻¹ :=
(eq_or_ne x 0).elim
  (λ h1, let h2 : (0 : R) = 0⁻¹ := inv_zero.symm in
    h1.symm ▸ h2 ▸ (zero_add (1 : R)).symm ▸ (good_map_one h).symm ▸ h2)
  (λ h1, eq_inv_of_mul_eq_one_left $ good_map_eq_zero h h0 $
    good_special_equality h $ inv_mul_cancel h1)

end division_ring



section field

variables {F : Type*} [field F]

/-- The general framework; reducing to injectivity. -/
lemma solution_of_map_zero_eq_one_imp_injective
  (h : ∀ f : F → F, good f → f 0 = 1 → injective f) {f : F → F} :
  good f ↔ (f = 0 ∨ f = has_sub.sub 1 ∨ (f = λ x, -(1 - x))) :=
⟨λ h0, or_iff_not_imp_left.mpr $ λ h1, (good_map_zero h0 h1).imp
    (λ h1, good_eq_of_inj h0 h1 $ h f h0 h1)
    (λ h1, let h2 := neg_eq_iff_eq_neg.mpr h1, h3 := good_neg h0 in
      neg_eq_iff_eq_neg.mp $ good_eq_of_inj h3 h2 $ h (-f) h3 h2),
λ h0, h0.elim (λ h1, h1.symm ▸ good_zero) $
  λ h1, h1.elim (λ h2, h2.symm ▸ good_one_sub) (λ h2, h2.symm ▸ good_neg good_one_sub)⟩



/-- Injectivity for `char(F) ≠ 2` -/
lemma case1_injective (h : (2 : F) ≠ 0) {f : F → F} (h0 : good f) (h1 : f 0 = 1) :
  injective f :=
have h2 : _ := good_shift2 h0 h1,
have h3 : ∀ y, f (f (-1) * f y) + (f y + 1) = f (-y),
  from λ y, h2 y ▸ neg_add_eq_sub 1 y ▸ (h0 (-1) y).trans (congr_arg f $ neg_one_mul y),
-- Reduce to `f(y) = f(-y) → y = 0`
suffices ∀ y, f y = f (-y) → y = 0,
  from λ a b h4, let h5 : f (-a) = f (-b) := (h3 a).symm.trans $ h4.symm ▸ h3 b in
    add_neg_eq_zero.mp $ this _ $ (eq_sub_of_add_eq' $ h0 a (-b)).trans $ mul_comm (-b) a ▸
    (neg_mul_comm b a).symm ▸ h4.symm ▸ h5 ▸ eq_sub_of_add_eq' (h0 b (-a)) ▸
    congr_arg f ((neg_add_rev _ _).trans $ congr_arg2 _ (neg_neg b) rfl).symm,
-- Prove that `f(y) = f(-y)` implies `y = 0`
let h4 := good_map_eq_zero_iff h0 h1 in λ y h5,
suffices 2 * f y = 2,
  from add_left_eq_self.mp $ (h4 _).mp $ (eq_sub_of_add_eq $ good_shift h0 h1 y).trans $
    sub_eq_zero_of_eq $ mul_left_cancel₀ h $ this.trans (mul_one _).symm,
suffices f (-1) = 2, from eq_add_of_sub_eq $ (h4 _).mp $ (h2 _).trans $
  add_right_eq_self.mp $ (add_left_comm (f y) _ _).trans $ this ▸ (h3 y).trans h5.symm,
zero_sub (1 : F) ▸ (h2 _).trans $ congr_arg2 _ h1 rfl



/-- Injectivity for `char(F) = 2` -/
lemma case2_injective (h : (2 : F) = 0) {f : F → F} (h0 : good f) (h1 : f 0 = 1) :
  injective f :=
have h2 : _ := good_shift h0 h1,
-- Start by changing the hypothesis to `f(a + 1) = f(b + 1)`
suffices ∀ a b, f (a + 1) = f (b + 1) → a = b,
  from λ a b h3, this _ _ $ add_left_injective 1 $ (h2 a).trans $ h3.trans (h2 b).symm,
-- Remove the cases where either `a = 0` or `b = 0` holds
have h3 : _ := good_map_eq_zero_iff h0 h1,
have h4 : ∀ c, f (c + 1) = 0 ↔ c = 0 := λ c, (h3 _).trans add_left_eq_self,
suffices ∀ a b, a ≠ 0 → b ≠ 0 → f (a + 1) = f (b + 1) → a = b,
  from λ a b h6, let h7 : a = 0 ↔ b = 0 := (h4 a).symm.trans $ h6.symm ▸ h4 b in
    (eq_or_ne a 0).elim (λ h8, h8.trans (h7.mp h8).symm)
      (λ h8, this a b h8 ((not_iff_not.mpr h7).mp h8) h6),
-- Reduce to showing that `f(CD + 1) = f(C + D)`, where `C = a + b + 1` and `D = a⁻¹ + b⁻¹ + 1`
λ a b h5 h6 h7,
suffices a + b = 0 ∨ a⁻¹ + b⁻¹ = 0,
  from let h8 : ∀ x : F, -x = x := λ x, (neg_one_mul x).symm.trans $
    (neg_eq_of_add_eq_zero_left h).symm ▸ one_mul x in
  this.elim (λ h9, (eq_neg_of_add_eq_zero_left h9).trans (h8 b))
    (λ h9, inv_inj.mp $ (eq_neg_of_add_eq_zero_left h9).trans (h8 _)),
suffices f (f (a + b + 1) * f (a⁻¹ + b⁻¹ + 1) + 1) = 0,
  from (mul_eq_zero.mp $ (h4 _).mp this).imp (h4 _).mp (h4 _).mp,
suffices f ((a + b + 1) * (a⁻¹ + b⁻¹ + 1) + 1) = f ((a + b + 1) + (a⁻¹ + b⁻¹ + 1)),
  from (eq_sub_of_add_eq $ h2 _).trans $ sub_eq_zero_of_eq $
    (eq_sub_of_add_eq $ h0 _ _).trans $ sub_eq_of_eq_add' $ this ▸ (h2 _).symm,
-- Start with the key step (see `h9`)
have h8 : _ := good_shift2 h0 h1,
have h9 : ∀ c d : F, d ≠ 0 → f (c + 1) = f (d + 1) →
    f ((c + 1) * (d⁻¹ + 1) - 1) = f ((c + 1) + (d⁻¹ + 1) - 1) :=
  λ c d h9 h10, suffices f ((c + 1) * (d⁻¹ + 1)) = f ((c + 1) + (d⁻¹ + 1)),
    from (h8 _).trans $ (h8 $ (c + 1) + (d⁻¹ + 1)).symm ▸ congr_arg2 _ this rfl,
  (h0 _ _).symm.trans $ add_left_eq_self.mpr $ h10.symm ▸
    good_special_equality h0 (mul_inv_cancel h9),
-- Reduce to showing three identities
suffices (a + 1 + (b⁻¹ + 1) - 1) + (b + 1 + (a⁻¹ + 1) - 1) = (a + b + 1) + (a⁻¹ + b⁻¹ + 1) ∧
    ((a + 1) * (b⁻¹ + 1) - 1) + ((b + 1) * (a⁻¹ + 1) - 1) = (a + b + 1) * (a⁻¹ + b⁻¹ + 1) + 1 ∧
    ((a + 1) * (b⁻¹ + 1) - 1) * ((b + 1) * (a⁻¹ + 1) - 1)
      = (a + 1 + (b⁻¹ + 1) - 1) * (b + 1 + (a⁻¹ + 1) - 1),
  from let U := a + 1 + (b⁻¹ + 1) - 1, V := b + 1 + (a⁻¹ + 1) - 1,
    W := (a + 1) * (b⁻¹ + 1) - 1, X := (b + 1) * (a⁻¹ + 1) - 1 in
  this.1 ▸ this.2.1 ▸ (eq_sub_of_add_eq' $ h0 W X).symm ▸ (eq_sub_of_add_eq' $ h0 U V).symm ▸ 
    congr_arg2 _ (congr_arg f this.2.2) (h9 a b h6 h7 ▸ h9 b a h5 h7.symm ▸ rfl),
-- Proof of identity 1
⟨by ring,
-- Proof of identity 2
by calc (a + 1) * (b⁻¹ + 1) - 1 + ((b + 1) * (a⁻¹ + 1) - 1) =
  (a + 1) * (b⁻¹ + 1) - 1 + ((b + 1) * (a⁻¹ + 1) - 1) + 2 * 2 :
  self_eq_add_right.mpr (mul_eq_zero_of_left h _)
... = (a + b + 1) * (a⁻¹ + b⁻¹ + 1) + (3 - (a * a⁻¹ + b * b⁻¹)) : by ring
... = (a + b + 1) * (a⁻¹ + b⁻¹ + 1) + 1 : congr_arg2 _ rfl $
  (mul_inv_cancel h5).symm ▸ (mul_inv_cancel h6).symm ▸ add_sub_cancel' 2 1,
-- Proof of identity 3
by calc ((a + 1) * (b⁻¹ + 1) - 1) * ((b + 1) * (a⁻¹ + 1) - 1) =
  (a * a⁻¹) * (b * b⁻¹) + (a + a⁻¹) * (b * b⁻¹) + (b + b⁻¹) * (a * a⁻¹)
    + (a + b⁻¹) * (b + a⁻¹) : by ring
... = 1 + (a + a⁻¹) + (b + b⁻¹) + (a + b⁻¹) * (b + a⁻¹) :
  (mul_inv_cancel h5).symm ▸ (mul_inv_cancel h6).symm ▸ (mul_one (a + a⁻¹)).symm ▸
    (mul_one (b + b⁻¹)).symm ▸ (mul_one (1 : F)).symm ▸ rfl
... = (a + 1 + (b⁻¹ + 1) - 1) * (b + 1 + (a⁻¹ + 1) - 1) : by ring⟩



/-- Injectivity -/
lemma map_zero_eq_one_imp_injective : ∀ f : F → F, good f → f 0 = 1 → injective f :=
  (ne_or_eq (2 : F) 0).elim case1_injective case2_injective

end field





/-- Final solution -/
theorem final_solution {F : Type*} [field F] {f : F → F} :
  good f ↔ (f = 0 ∨ f = has_sub.sub 1 ∨ (f = λ x, -(1 - x))) :=
  solution_of_map_zero_eq_one_imp_injective map_zero_eq_one_imp_injective

end IMO2017A6
end IMOSL
