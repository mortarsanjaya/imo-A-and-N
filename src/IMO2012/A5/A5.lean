import
  ring_theory.ideal.quotient
  logic.lemmas
  IMO2012.A5.explicit_rings.F2
  IMO2012.A5.explicit_rings.F2e
  IMO2012.A5.explicit_rings.F3
  IMO2012.A5.explicit_rings.F4
  IMO2012.A5.explicit_rings.Z4

/- # IMO 2012 A5 -/

namespace IMOSL
namespace IMO2012A5

open function

/-- The definition -/
def good {R S : Type*} [ring R] [ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y









/- ### Step 0: Answer -/

section extra_maps

variables (R : Type*) [ring R] 

def 𝔽₂_map : 𝔽₂ → R
| 𝔽₂.O := -1
| 𝔽₂.I := 0

def 𝔽₂ε_map : 𝔽₂ε → R
| 𝔽₂ε.O := -1
| 𝔽₂ε.I := 0
| 𝔽₂ε.X := 1
| 𝔽₂ε.Y := 0

def 𝔽₃_map1 : 𝔽₃ → R
| 𝔽₃.𝔽₃0 := -1
| 𝔽₃.𝔽₃1 := 0
| 𝔽₃.𝔽₃2 := 1

def 𝔽₃_map2 : 𝔽₃ → R
| 𝔽₃.𝔽₃0 := -1
| 𝔽₃.𝔽₃1 := 0
| 𝔽₃.𝔽₃2 := 0

def 𝔽₄_map (φ : R) : 𝔽₄ → R
| 𝔽₄.O := -1
| 𝔽₄.I := 0
| 𝔽₄.X := φ
| 𝔽₄.Y := 1 - φ

def ℤ₄_map : ℤ₄ → R
| ℤ₄.ℤ₄0 := -1
| ℤ₄.ℤ₄1 := 0
| ℤ₄.ℤ₄2 := 1
| ℤ₄.ℤ₄3 := 0

end extra_maps



section answer_checking

variables {R : Type*} [ring R]

/-- The zero map is good. -/
lemma zero_is_good {S : Type*} [ring S] : good (0 : R → S) :=
  λ _ _, (sub_self 0).trans (mul_zero 0).symm

/-- The map `x ↦ x - 1` is good. -/
lemma sub_one_is_good : good (λ x : R, x - 1) :=
  λ x y, (sub_sub_sub_cancel_right _ _ 1).trans $ sub_sub_sub_eq (x * y) x y 1 ▸ 
    mul_sub_one x y ▸ (sub_one_mul x (y - 1)).symm

/-- The map `𝔽₂_map` is good. -/
theorem 𝔽₂_map_is_good : good (𝔽₂_map R)
| 𝔽₂.O x := (zero_sub (𝔽₂_map R x)).trans (neg_one_mul (𝔽₂_map R x)).symm
| 𝔽₂.I x := (zero_mul (𝔽₂_map R x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (𝔽₂_map R) (add_comm x 1)

/-- The map `x ↦ x^2 - 1` is good if `R` is commutative. -/
theorem sq_sub_one_is_good {R : Type*} [comm_ring R] : good (λ x : R, x ^ 2 - 1) :=
λ x y, suffices (x * y + 1) ^ 2 - (x + y) ^ 2 = (x ^ 2 - 1) * (y ^ 2 - 1),
  from (sub_sub_sub_cancel_right _ _ _).trans this,
by ring

/-- The map `𝔽₂ε_map` is good. -/
theorem 𝔽₂ε_map_is_good : good (𝔽₂ε_map R)
| 𝔽₂ε.O x := (zero_sub (𝔽₂ε_map R x)).trans (neg_one_mul (𝔽₂ε_map R x)).symm
| 𝔽₂ε.I x := (zero_mul (𝔽₂ε_map R x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (𝔽₂ε_map R) (add_comm x 1)
| 𝔽₂ε.X 𝔽₂ε.O := (zero_sub 1).trans (one_mul (-1)).symm
| 𝔽₂ε.X 𝔽₂ε.I := (sub_self 0).trans (one_mul 0).symm
| 𝔽₂ε.X 𝔽₂ε.X := (zero_sub (-1)).trans $ (neg_neg 1).trans (one_mul 1).symm
| 𝔽₂ε.X 𝔽₂ε.Y := (sub_self 0).trans (one_mul 0).symm
| 𝔽₂ε.Y 𝔽₂ε.O := (sub_self 0).trans (zero_mul (-1)).symm
| 𝔽₂ε.Y 𝔽₂ε.I := (sub_self 1).trans (zero_mul 0).symm
| 𝔽₂ε.Y 𝔽₂ε.X := (sub_self 0).trans (zero_mul 1).symm
| 𝔽₂ε.Y 𝔽₂ε.Y := (sub_self (-1)).trans (zero_mul 0).symm

/-- The map `𝔽₃_map1` is good. -/
theorem 𝔽₃_map1_is_good : good (𝔽₃_map1 R)
| 𝔽₃.𝔽₃0 x := (zero_sub (𝔽₃_map1 R x)).trans (neg_one_mul (𝔽₃_map1 R x)).symm
| 𝔽₃.𝔽₃1 x := (zero_mul (𝔽₃_map1 R x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (𝔽₃_map1 R) (add_comm x 1)
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃0 := (zero_sub 1).trans (mul_neg_one 1).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃1 := (sub_self (-1)).trans (mul_zero 1).symm 
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃2 := (sub_zero 1).trans (mul_one 1).symm

/-- The map `𝔽₃_map2` is good. -/
theorem 𝔽₃_map2_is_good : good (𝔽₃_map2 R)
| 𝔽₃.𝔽₃0 x := (zero_sub (𝔽₃_map2 R x)).trans (neg_one_mul (𝔽₃_map2 R x)).symm
| 𝔽₃.𝔽₃1 x := (zero_mul (𝔽₃_map2 R x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (𝔽₃_map2 R) (add_comm x 1)
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃0 := (sub_self 0).trans (zero_mul (-1)).symm
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃1 := (sub_self (-1)).trans (mul_zero 0).symm 
| 𝔽₃.𝔽₃2 𝔽₃.𝔽₃2 := (sub_zero 0).trans (mul_zero 0).symm

/-- The map `𝔽₄_map` is good. -/
theorem 𝔽₄_map_is_good {φ : R} (h : φ * (1 - φ) = -1) : good (𝔽₄_map R φ)
| 𝔽₄.O x := (zero_sub (𝔽₄_map R φ x)).trans (neg_one_mul (𝔽₄_map R φ x)).symm
| 𝔽₄.I x := (zero_mul (𝔽₄_map R φ x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (𝔽₄_map R φ) (add_comm x 1)
| 𝔽₄.X 𝔽₄.O := (zero_sub φ).trans (mul_neg_one φ).symm
| 𝔽₄.X 𝔽₄.I := (sub_self (1 - φ)).trans (mul_zero φ).symm
| 𝔽₄.X 𝔽₄.X := sub_eq_of_eq_add $ eq_add_of_sub_eq' $ (mul_one_sub φ φ).symm.trans h
| 𝔽₄.X 𝔽₄.Y := (sub_zero (-1)).trans h.symm
| 𝔽₄.Y 𝔽₄.O := (zero_sub (1 - φ)).trans (mul_neg_one (1 - φ)).symm
| 𝔽₄.Y 𝔽₄.I := (sub_self φ).trans (mul_zero (1 - φ)).symm
| 𝔽₄.Y 𝔽₄.X := (sub_zero (-1)).trans $ h.symm.trans $
    (commute.one_right φ).sub_right (commute.refl φ)
| 𝔽₄.Y 𝔽₄.Y := sub_eq_of_eq_add $ eq_add_of_sub_eq' $
    (one_sub_mul _ _).symm.trans $ (congr_arg (* (1 - φ)) (sub_sub_cancel 1 φ)).trans h

/-- The map `ℤ₄_map` is good. -/
theorem ℤ₄_map_is_good : good (ℤ₄_map R)
| ℤ₄.ℤ₄0 x := (zero_sub (ℤ₄_map R x)).trans (neg_one_mul (ℤ₄_map R x)).symm
| ℤ₄.ℤ₄1 x := (zero_mul (ℤ₄_map R x)).symm ▸
    sub_eq_zero_of_eq $ congr_arg (ℤ₄_map R) (add_comm x 1)
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄0 := (zero_sub 1).trans (one_mul (-1)).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄1 := (sub_self 0).trans (mul_zero 1).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄2 := (zero_sub (-1)).trans $ (neg_neg 1).trans (mul_one 1).symm
| ℤ₄.ℤ₄2 ℤ₄.ℤ₄3 := (sub_self 0).trans (mul_zero 1).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄0 := (sub_self 0).trans (zero_mul (-1)).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄1 := (sub_self (-1)).trans (zero_mul 0).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄2 := (sub_self 0).trans (zero_mul 1).symm
| ℤ₄.ℤ₄3 ℤ₄.ℤ₄3 := (sub_self 1).trans (zero_mul 0).symm

end answer_checking









/- ### Step 1: Small observations -/

section hom

variables {R R₀ S : Type*} [ring R] [ring R₀] [ring S]

/-- Given `f : R → S` good and `φ : R₀ →+* R`, `f ∘ φ` is good as well. -/
lemma good_map_comp_hom {f : R → S} (h : good f) (φ : R₀ →+* R) : good (f ∘ φ) :=
  λ x y, h (φ x) (φ y) ▸ congr_arg2 _
    (congr_arg f $ (φ.map_add _ _).trans $ congr_arg2 _ (φ.map_mul x y) φ.map_one)
    (congr_arg f $ φ.map_add x y)

/-- Given `f : R → S` and `φ : R₀ →+* R`, `f` is good if `φ` is surjective and `f ∘ φ` is good. -/
lemma good_of_comp_hom_good_surjective
  {φ : R₀ →+* R} (h : surjective φ) {f : R → S} (h0 : good (f ∘ φ)) : good f :=
  λ x y, exists.elim (h x) $ λ a h1, exists.elim (h y) $ λ b h2,
  h1 ▸ h2 ▸ h0 a b ▸ congr_arg2 _
    (congr_arg f $ (φ.map_add (a * b) 1).symm ▸ congr_arg2 _ (φ.map_mul a b).symm φ.map_one.symm)
    (congr_arg f (φ.map_add a b).symm)

end hom


section noncomm

variables {R S : Type*} [ring R] [ring S] [is_domain S] {f : R → S} (h : good f)
include h

lemma good_map_one : f 1 = 0 :=
  mul_self_eq_zero.mp $ (h 1 1).symm.trans $ sub_eq_zero.mpr $
    congr_arg f $ (add_left_inj 1).mpr (mul_one 1)

lemma neg_map_zero_mul (x : R) : -f 0 * f x = f x :=
  by rw [neg_mul, ← h, zero_mul, zero_add, zero_add, good_map_one h, zero_sub, neg_neg]

/-- (1.1) -/
lemma eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = 0 :=
  funext $ λ x, (mul_left_eq_self₀.mp $ neg_map_zero_mul h x).resolve_left $
    λ h1, h0 $ neg_eq_iff_eq_neg.mp h1

lemma one_ne_zero_of_map_zero (h0 : f 0 = -1) : (1 : R) ≠ 0 :=
  mt (congr_arg f) $ ne_of_eq_of_ne (good_map_one h) $
    ne_of_ne_of_eq (neg_ne_zero.mpr one_ne_zero).symm h0.symm

/-- (1.2) -/
lemma map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) :=
  h x (-1) ▸ congr_arg2 _
    (congr_arg f $ (neg_add_eq_sub x 1).symm.trans $ congr_arg2 _ (mul_neg_one x).symm rfl)
    (congr_arg f $ sub_eq_add_neg x 1)

/-- (1.3) -/
lemma map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) :=
  (congr_arg2 (λ u v, f v - f u) (add_sub_cancel x 1).symm
    ((sub_add_cancel' 1 x).symm.trans $ congr_arg (has_sub.sub 1) (add_comm 1 x))).trans $
  map_neg_sub_map1 h (x + 1)

/-- Auxiliary lemma for two sub-cases -/
theorem eq_hom_sub_one_of (h0 : f 0 = -1) (h1 : ∀ x y, f (x + y) = f x + f y + 1) :
  ∃ φ : R →+* S, f = λ x, φ x - 1 :=
⟨⟨λ x, f x + 1,
  add_left_eq_self.mpr $ good_map_one h,
  λ x y, let h2 : f (x * y + 1) = f (x * y) + 1 :=
    (h1 _ _).trans $ (good_map_one h).symm ▸ (add_zero $ f (x * y)).symm ▸ rfl in
    by rw [← h2, eq_add_of_sub_eq (h x y), h1,
      add_assoc, ← add_assoc, ← mul_add_one, ← add_one_mul],
  add_eq_zero_iff_eq_neg.mpr h0,
  λ x y, by rw [h1, add_assoc, add_add_add_comm]⟩,
funext (λ x, (add_sub_cancel (f x) 1).symm)⟩

end noncomm









/- ### Step 2: Ring quotient -/

section quot

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S] {f : R → S} (h : good f)
include h

lemma quasi_period_iff {c : R} : (∀ x, f (c + x) = -f c * f x) ↔ (∀ x, f (c * x + 1) = 0) :=  
  forall_congr $ λ x, by rw [neg_mul, ← h, neg_sub, eq_comm]; exact sub_eq_self

lemma quasi_period_add {c d : R} (h0 : ∀ x, f (c * x + 1) = 0) (h1 : ∀ x, f (d * x + 1) = 0) :
 ∀ x, f ((c + d) * x + 1) = 0 :=
  by rw ← quasi_period_iff h at h0 h1 ⊢; intros x;
    rw [h0, add_assoc, h0, h1, ← mul_assoc, ← mul_neg]

lemma map_quasi_period (h0 : f 0 = -1) {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) :
  f c = 1 ∨ f c = -1 :=
suffices f (-c) = f c, from mul_self_eq_one_iff.mp $ neg_injective $
  (neg_mul (f c) (f c)).symm.trans $ (congr_arg2 _ rfl this.symm).trans $
  (h1 (-c)).symm.trans $ (add_neg_self c).symm ▸ h0,
  let h2 := h (c + 1) (-1) in by rwa [h1, good_map_one h, mul_zero, zero_mul,
    sub_eq_zero, add_one_mul, neg_add_cancel_right, add_neg_cancel_right, mul_neg_one] at h2

lemma map_quasi_period_ne_zero (h0 : f 0 = -1) {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) :
  f c ≠ 0 :=
  (map_quasi_period h h0 h1).elim (λ h2 h3, one_ne_zero $ h2.symm.trans h3)
    (λ h2 h3, neg_ne_zero.mpr one_ne_zero $ h2.symm.trans h3)

/-- (2.1) The ideal of quasi-periods -/
def quasi_period_ideal : ideal R :=
{ carrier := {c | ∀ x, f (c * x + 1) = 0},
  add_mem' := λ a b, quasi_period_add h,
  zero_mem' := λ x, (congr_arg f $ add_left_eq_self.mpr $ zero_mul x).trans (good_map_one h),
  smul_mem' := λ a b h1 x, (congr_arg (λ x, f (x + 1)) $
    by rw [smul_eq_mul, mul_comm a b, mul_assoc]).trans (h1 $ a * x) }

lemma mem_quasi_period_ideal_iff {c : R} :
  c ∈ quasi_period_ideal h ↔ ∀ x, f (c + x) = -f c * f x :=
  (quasi_period_iff h).symm

lemma period_iff {c : R} : (∀ x, f (c + x) = f x) ↔ ((∀ x, f (c + x) = -f c * f x) ∧ f c = f 0) :=
  ⟨λ h0, let h1 : f c = f 0 := (congr_arg f (add_zero c).symm).trans (h0 0) in
    ⟨λ x, (h0 x).trans $ (neg_map_zero_mul h x).symm.trans $
      congr_arg2 _ (congr_arg _ h1.symm) rfl, h1⟩,
  λ h0 x, (h0.1 x).trans $ (congr_arg (λ t, -t * f x) h0.2).trans $ neg_map_zero_mul h x⟩

lemma period_imp_quasi_period {c : R} (h0 : ∀ x, f (c + x) = f x) :
  ∀ x, f (c * x + 1) = 0 :=
  (quasi_period_iff h).mp ((period_iff h).mp h0).1

lemma period_mul {c : R} (h0 : ∀ x, f (c + x) = f x) : ∀ d x, f (d * c + x) = f x :=
  (ne_or_eq (f 0) (-1)).elim (λ h1 d x, (eq_zero_of_map_zero_ne_neg_one h h1).symm ▸ rfl) $
λ h1, suffices ∀ d, (∃ x, f (d * x + 1) ≠ 0) → ∀ x, f (d * c + x) = f x,
---- First prove the lemma assuming that it holds whenever `d ∉ quasi_period_ideal`
from λ d, (em' $ ∀ x, f (d * x + 1) = 0).elim (λ h2, this d $ not_forall.mp h2) $
  λ h2 x, this (d - 1) (⟨1, map_quasi_period_ne_zero h h1 $ (quasi_period_iff h).mpr $
      by rwa [mul_one, sub_add_cancel]⟩) x ▸ h0 ((d - 1) * c + x) ▸
    congr_arg f (by rw [← add_assoc, ← one_add_mul, add_sub_cancel'_right]),
---- Now prove the lemma for `d ∉ quasi_period_ideal`
λ d h2, begin
  cases h2 with x h2,
  have h3 := h d (c + x),
  rw [h0, add_left_comm, h0, ← h, sub_left_inj, mul_add, add_assoc] at h3,
  rw [period_iff h, quasi_period_iff h] at h0 ⊢,
  refine ⟨λ x, h0.1 (d * x) ▸ congr_arg f (congr_arg2 _ (by rw [mul_comm d c, mul_assoc]) rfl), _⟩,
  rwa [(mem_quasi_period_ideal_iff h).mp (ideal.mul_mem_left _ d h0.1),
       mul_left_eq_self₀, or_iff_left h2, neg_eq_iff_eq_neg, ← h1] at h3
end

/-- (2.2) The ideal of periods -/
def period_ideal : ideal R :=
{ carrier := {c | ∀ x, f (c + x) = f x},
  add_mem' := λ a b h1 h2 x, (congr_arg f $ add_assoc a b x).trans $ (h1 (b + x)).trans (h2 x),
  zero_mem' := λ x, congr_arg f $ zero_add x,
  smul_mem' := λ d c h0, period_mul h h0 d }

lemma period_ideal_le_quasi_period_ideal : period_ideal h ≤ quasi_period_ideal h :=
  λ _, period_imp_quasi_period h

lemma period_equiv_imp_f_eq {a b : R} (h0 : ideal.quotient.ring_con (period_ideal h) a b) :
  f a = f b :=
  (congr_arg f (sub_add_cancel a b).symm).trans $
    ideal.quotient.eq.mp ((ring_con.eq _).mpr h0) b

/-- Lifting of `f` along the ideal of periods. -/
def period_lift : R ⧸ period_ideal h → S :=
  quot.lift f $ λ a b, period_equiv_imp_f_eq h

lemma period_lift_is_good : good (period_lift h) :=
  good_of_comp_hom_good_surjective ideal.quotient.mk_surjective h

lemma period_lift_comp_quotient_eq_f :
  period_lift h ∘ ideal.quotient.mk (period_ideal h) = f := rfl

lemma zero_of_periodic_period_lift :
  ∀ c : R ⧸ period_ideal h, (∀ x, period_lift h (c + x) = period_lift h x) → c = 0 :=
  quot.ind $ by intros c h0;
    exact ideal.quotient.eq_zero_iff_mem.mpr (λ y, h0 $ quot.mk _ y)



/-!
##### Extra structure given a non-period, quasi-period element

The results in this mini-subsection is useful for Subcase 2.2 and 2.4.
-/

section quasi_period

variables {c : R} (h0 : f 0 = -1) (h1 : c ∈ quasi_period_ideal h) (h2 : c ∉ period_ideal h)
include h0 h1 h2

lemma map_nonperiod_quasi_period : f c = 1 :=
  let h3 := (quasi_period_iff h).mpr h1 in (map_quasi_period h h0 h3).elim id $
    λ h4, false.elim $ h2 $ λ x, by rw [h3, h4, neg_neg, one_mul]

lemma map_quasi_period_add (x : R) : f (c + x) = -f x :=
  ((quasi_period_iff h).mpr h1 x).trans $
    (map_nonperiod_quasi_period h h0 h1 h2).symm ▸ neg_one_mul (f x)

lemma is_period_or_eq_quasi_nonperiod {d : R} (h3 : d ∈ quasi_period_ideal h) :
  d ∈ period_ideal h ∨ d - c ∈ period_ideal h :=
  or_iff_not_imp_left.mpr $ λ h4 x, by rw [← neg_inj, ← map_quasi_period_add h h0 h1 h2,
    ← add_assoc, add_sub_cancel'_right, map_quasi_period_add h h0 h3 h4]

lemma mul_nonquasi_period_is_nonperiod {d : R} (h3 : d ∉ quasi_period_ideal h) :
  d * c ∉ period_ideal h :=
exists.elim (not_forall.mp h3) $ λ x h3, not_forall.mpr
⟨d * x + 1, (eq_or_ne (-1 : S) 1).elim
---- First get rid of the case `-1 = 1 ∈ S`
(λ h4, false.elim $ h2 $ (period_iff h).mpr ⟨(quasi_period_iff h).mpr h1,
  (map_nonperiod_quasi_period h h0 h1 h2).trans (h0.trans h4).symm⟩) $
---- Now the main case
(λ h4, let h5 := map_quasi_period_add h h0 h1 h2 in
  by rw [← add_assoc, ← mul_add, eq_add_of_sub_eq (h d _), h5, add_left_comm, h5, mul_neg,
    ← neg_add, ← eq_add_of_sub_eq (h d x), ← neg_one_mul, mul_left_eq_self₀, not_or_distrib];
  exact ⟨h4, h3⟩)⟩
  
lemma equiv_mod_quasi_period_ideal (x : R) :
  x ∈ quasi_period_ideal h ∨ x - 1 ∈ quasi_period_ideal h :=
  let h3 : ∀ y : R, y * c ∈ period_ideal h → y ∈ quasi_period_ideal h :=
    λ y, (not_imp_not.mp $ mul_nonquasi_period_is_nonperiod h h0 h1 h2) in
  or.imp (h3 x) (h3 (x - 1)) $ (sub_one_mul x c).symm ▸
    is_period_or_eq_quasi_nonperiod h h0 h1 h2 (ideal.mul_mem_left _ x h1)

lemma equiv_mod_period_ideal (x : R) : (x ∈ period_ideal h ∨ x - c ∈ period_ideal h) ∨
  x - 1 ∈ period_ideal h ∨ x - (c + 1) ∈ period_ideal h :=
  let h3 : ∀ x : R, x ∈ quasi_period_ideal h → (x ∈ period_ideal h ∨ x - c ∈ period_ideal h) :=
    λ x, is_period_or_eq_quasi_nonperiod h h0 h1 h2 in
  (equiv_mod_quasi_period_ideal h h0 h1 h2 x).imp (h3 x)
    (by rw [add_comm, ← sub_sub]; exact h3 (x - 1))

end quasi_period

lemma cases_of_nonperiod_quasi_period (h0 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
  {c : R} (h1 : f 0 = -1) (h2 : c ∈ quasi_period_ideal h) (h3 : c ≠ 0) (x : R) :
  (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 :=
  (equiv_mod_period_ideal h h1 h2 (mt (h0 c) h3) x).imp
    (or.imp (h0 x) (λ h5, eq_of_sub_eq_zero $ h0 _ h5))
    (or.imp (λ h5, eq_of_sub_eq_zero $ h0 _ h5) (λ h5, eq_of_sub_eq_zero $ h0 _ h5))

end quot









/- ### Step 3: Case 1: `f(-1) ≠ 0` -/

section step3

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S] {f : R → S} (h : good f)
include h

/-- (3.6) While this lemma does not depend on `f(-1) ≠ 0`,
  it is useless in the case `f(-1) = 0`. -/
lemma case1_map_add_main_eq1 (x y : R) :
  f (x + y) - f (-(x + y)) = f (-x) * f (-y) - f x * f y :=
  (sub_sub_sub_cancel_left _ _ (f (x * y + 1))).symm.trans $ congr_arg2 _
    (h (-x) (-y) ▸ congr_arg2 _ (by rw neg_mul_neg) (congr_arg f $ neg_add x y)) (h x y)

/-- (3.7) While this lemma does not depend on `f(-1) ≠ 0`,
  it is useless in the case `f(-1) = 0`. -/
lemma case1_map_add_main_eq2 (x y : R) :
  -(f (x + y + 1) * f (-1)) = f (-x) * f (-y) - f x * f y :=
  (congr_arg _ (map_neg_sub_map2 h _).symm).trans $
    (neg_sub _ _).trans $ case1_map_add_main_eq1 h x y


variables (h0 : f (-1) ≠ 0)
include h0

/-- (3.1) -/
lemma case1_map_neg_add_one (x : R) : f (-x + 1) = -f (x + 1) :=
  let h1 := map_neg_sub_map2 h in
  mul_right_cancel₀ h0 $ (h1 (-x)).symm.trans $ (neg_neg x).symm ▸
    (neg_sub _ _).symm.trans $ (congr_arg _ $ h1 x).trans (neg_mul _ _).symm

lemma case1_map_zero : f 0 = -1 :=
  by_contra $ λ h1, h0 $ congr_fun (eq_zero_of_map_zero_ne_neg_one h h1) _

/-- (3.2) -/
lemma case1_map_two : f 2 = 1 :=
  neg_injective $ (case1_map_neg_add_one h h0 1).symm.trans $
    (neg_add_self (1 : R)).symm ▸ case1_map_zero h h0

/-- (3.3) -/
lemma case1_map_add_one_add_map_sub_one (x : R) :
  f (x + 1) + f (x - 1) = -(f x * f (-1)) :=
  neg_eq_iff_eq_neg.mp $ (neg_add' _ _).trans $ case1_map_neg_add_one h h0 x ▸
    map_neg_sub_map1 h x ▸ congr_arg2 _ (congr_arg f $ neg_add_eq_sub x 1) rfl 

/-- (3.4) -/
lemma case1_map_two_mul_add_one1 (x : R) : f (2 * x + 1) = f x - f (-x) :=
suffices f (2 + x) = -f (-x),
  from (eq_add_of_sub_eq $ h 2 x).trans $ (sub_eq_add_neg (f x) (f (-x))).symm ▸
    congr_arg2 _ ((case1_map_two h h0).symm ▸ one_mul (f x)) this,
neg_eq_iff_eq_neg.mp $ add_right_comm 1 x 1 ▸ (case1_map_neg_add_one h h0 _).symm.trans $
  congr_arg f $ (neg_add_eq_sub (1 + x) 1).trans (sub_add_cancel' 1 x)

/-- (3.5) -/
lemma case1_map_two_mul_add_one2 (x : R) : f (2 * x + 1) = -(f (x + 1) * f (-1)) :=
  (case1_map_two_mul_add_one1 h h0 x).trans $
    (neg_sub _ _).symm.trans $ congr_arg _ $ map_neg_sub_map2 h x

/-- Main claim -/
lemma case1_map_neg_one_cases : f (-1) = -2 ∨ f (-1) = 1 :=
begin
  have h1 := case1_map_neg_add_one h h0 (1 + 1 : R),
  rw [neg_add_eq_sub, sub_add_cancel'] at h1,
  have h2 := case1_map_add_one_add_map_sub_one h h0,
  have h3 := h2 (2 * (1 + 1) : R),
  rw [case1_map_two_mul_add_one2 h h0, two_mul, add_sub_assoc, add_sub_cancel,
      ← add_assoc, eq_sub_of_add_eq (h2 (1 + 1 + 1 : R)), add_sub_cancel, ← neg_mul, ← h1,
      ← neg_eq_iff_eq_neg.mpr h1, ← bit0, case1_map_two h h0, eq_neg_iff_add_eq_zero] at h3,
  suffices : (f (-1) + 2) * (f (-1) - 1) * f (-1) = 0,
    rwa [mul_eq_zero, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_iff_left h0] at this,
  rw ← h3; ring
end

/-- (3.8) -/
lemma case1_map_add_one_ne_zero_imp {x : R} (h1 : f (x + 1) ≠ 0) : f (-x) + f x = f (-1) :=
begin
  have h2 := (case1_map_add_main_eq2 h x x).symm,
  rw [mul_self_sub_mul_self, ← two_mul, case1_map_two_mul_add_one2 h h0,
      map_neg_sub_map2 h, neg_mul, neg_neg, mul_comm, mul_eq_mul_left_iff] at h2,
  exact h2.resolve_right (mul_ne_zero h1 h0)
end

/-- (3.9) -/
lemma case1_map_add_one_eq_zero_imp {x : R} (h1 : f (x + 1) = 0) : f x = -1 ∧ f (-x) = -1 := 
begin
  have h2 := map_neg_sub_map2 h x,
  rw [h1, zero_mul, sub_eq_zero] at h2,
  have h3 := case1_map_two_mul_add_one2 h h0,
  have h4 := case1_map_add_main_eq1 h x (x + 1),
  rw [h1, mul_zero, sub_zero, ← add_assoc, ← two_mul, h3, h1, zero_mul, neg_zero, zero_sub,
      ← sub_add_cancel'' (1 : R), add_assoc, ← bit0, ← mul_add_one, ← neg_add_eq_sub,
      ← mul_neg, h3, neg_neg, neg_add_eq_sub, sub_add_cancel'', h2] at h4,
  have h5 := case1_map_add_main_eq2 h x (-(x + 1)),
  rw [neg_neg, h1, mul_zero, zero_sub, neg_inj, add_right_comm, add_neg_self, ← h4,
      mul_eq_mul_right_iff, case1_map_zero h h0, or_iff_left h0, eq_comm] at h5,
  exact ⟨h5, h2.trans h5⟩
end

end step3









/- ### Step 4: Subcase 1.1: `f(-1) = -2 ≠ 0` -/

section step4

/-- Auxiliary lemma: `2 ≠ 0` -/
lemma case1_1_S_two_ne_zero {S : Type*} [add_group S]
  {a b : S} (h : a ≠ 0) (h0 : a = -b) : (b : S) ≠ 0 :=
  neg_ne_zero.mp $ λ h1, h $ h0.trans h1

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) = -2)
include h h0 h1

/-- (4.1) -/
lemma case1_1_lem1 (x : R) : f (-x) + f x = -2 :=
  (ne_or_eq (f (x + 1)) 0).elim
    (λ h2, (case1_map_add_one_ne_zero_imp h h0 h2).trans h1)
    (λ h2, let h3 := case1_map_add_one_eq_zero_imp h h0 h2 in
      (congr_arg2 _ h3.2 h3.1).trans (neg_add _ _).symm)

/-- (4.2) -/
lemma case1_1_lem2 (x : R) : f (x + 1) = f x + 1 :=
  let h2 := congr_arg2 has_sub.sub (case1_1_lem1 h h0 h1 x) (map_neg_sub_map2 h x) in
  by rw [add_sub_sub_cancel, h1, mul_neg, ← neg_sub', neg_sub,
    ← sub_one_mul, ← mul_two, mul_eq_mul_right_iff] at h2;
  exact h2.elim (λ h2, (add_eq_of_eq_sub h2).symm)
  (λ h2, absurd h2 $ case1_1_S_two_ne_zero h0 h1)

/-- Solution for the current subcase -/
theorem case1_1_sol : ∃ φ : R →+* S, f = λ x, φ x - 1 :=
eq_hom_sub_one_of h (case1_map_zero h h0) $ λ x y, begin
  have h2 := λ t, eq_sub_of_add_eq (case1_1_lem1 h h0 h1 t),
  have h3 := case1_map_add_main_eq2 h x y,
  rw [h1, h2, h2, case1_1_lem2 h h0 h1, mul_neg, neg_neg, add_one_mul] at h3,
  refine mul_right_cancel₀ (case1_1_S_two_ne_zero h0 h1) ((eq_sub_of_add_eq h3).trans _),
  ring
end

end step4









/- ### Step 5: Subcase 1.2: `f(-1) = 1 ≠ -2` -/

section step5

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) ≠ -2)
include h h0 h1

/-- (5.1) -/
lemma case1_2_lem1 (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
  {c : R} (h3 : f (c + 1) = 0) : c = 0 :=
  h2 c $ λ x, let h4 := case1_map_add_main_eq2 h c (x - 1),
    h5 := case1_map_add_one_eq_zero_imp h h0 h3 in
  by rw [h5.1, h5.2, ← mul_sub, neg_one_mul, neg_inj, map_neg_sub_map2 h,
    add_assoc, sub_add_cancel, mul_eq_mul_right_iff] at h4;
  exact h4.resolve_right h0

variables (h2 : f (-1) = 1)
include h2

section quotient

variables (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h3

/-- (5.2) -/
lemma case1_2_lem2 (x : R) : f (x + 1) + f (x - 1) + f x = 0 :=
  add_eq_zero_iff_eq_neg.mpr $ (case1_map_add_one_add_map_sub_one h h0 x).trans $
    congr_arg _ $ h2.symm ▸ mul_one (f x)

/-- `3 = 0` in `R` -/
lemma case1_2_lem3 : (3 : R) = 0 := 
  h3 (3 : R) $ let h4 := case1_2_lem2 h h0 h1 h2 h3 in λ x,
    let h5 := h4 (x + 1 + 1) in by rwa [add_sub_cancel, add_right_comm,
      ← h4 (x + 1), add_left_inj, add_sub_cancel, add_comm, add_right_inj,
      add_assoc x 1 1, ← bit0, add_rotate, ← bit1] at h5

/-- (5.3) -/
lemma case1_2_lem4 (x : R) (h4 : x ≠ 0) : f (-x) + f x = 1 :=
  h2 ▸ case1_map_add_one_ne_zero_imp h h0 (mt (case1_2_lem1 h h0 h1 h3) h4)

/-- The main lemma for the subcase -/
lemma case1_2_lem5 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 :=
begin
  by_contra' h4,
  rw ← add_eq_zero_iff_eq_neg at h4,
  have h5 := case1_2_lem4 h h0 h1 h2 h3,
  have h6 := congr_arg2 has_add.add (h5 (x + 1) h4.2.2) (h5 (x - 1) $ sub_ne_zero_of_ne h4.2.1),
  have h7 := λ x, eq_neg_of_add_eq_zero_left (case1_2_lem2 h h0 h1 h2 h3 x),
  rw [add_add_add_comm, h7, add_comm (f (-(x + 1))), neg_sub',
      sub_neg_eq_add, neg_add', h7, ← neg_add, ← bit0, h5 x h4.1] at h6,
  exact h1 (h2.trans $ neg_eq_iff_eq_neg.mp h6)
end


lemma case1_2_𝔽₃_hom_bijective :
  bijective (𝔽₃.cast_hom $ case1_2_lem3 h h0 h1 h2 h3) :=
  ⟨𝔽₃.cast_hom_injective _ (one_ne_zero_of_map_zero h $ case1_map_zero h h0),
  λ x, (case1_2_lem5 h h0 h1 h2 h3 x).elim (λ h4, ⟨𝔽₃.𝔽₃0, h4.symm⟩) $
    λ h4, h4.elim (λ h4, ⟨𝔽₃.𝔽₃1, h4.symm⟩) (λ h4, ⟨𝔽₃.𝔽₃2, h4.symm⟩)⟩

lemma case1_2_quotient_sol :
  f = 𝔽₃_map1 S ∘
    (ring_equiv.of_bijective _ $ case1_2_𝔽₃_hom_bijective h h0 h1 h2 h3).symm :=
  (mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x,
  match x with
  | 𝔽₃.𝔽₃0 := case1_map_zero h h0
  | 𝔽₃.𝔽₃1 := good_map_one h
  | 𝔽₃.𝔽₃2 := h2
  end

end quotient


lemma case1_2_lift_decomp : ∃ φ : R ⧸ period_ideal h ≃+* 𝔽₃, period_lift h = 𝔽₃_map1 S ∘ φ :=
  ⟨_, case1_2_quotient_sol (period_lift_is_good h) h0 h1 h2 (zero_of_periodic_period_lift h)⟩

/-- Solution for the current subcase -/
theorem case1_2_sol : ∃ φ : R →+* 𝔽₃, surjective φ ∧ f = 𝔽₃_map1 S ∘ φ :=
  exists.elim (case1_2_lift_decomp h h0 h1 h2) $
    λ ψ h2, let π := ideal.quotient.mk (period_ideal h) in
    ⟨ψ.to_ring_hom.comp π, ψ.surjective.comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h2⟩

end step5









/- ### Step 6: Case 2: `f(-1) = 0` -/

section step6

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

/-- (6.1) `f` is even -/
lemma case2_map_even (x : R) : f (-x) = f x :=
  eq_of_sub_eq_zero $ (map_neg_sub_map2 h x).trans $ mul_eq_zero_of_right _ h0

/-- (6.2) -/
lemma case2_good_alt (x y : R) : f (x * y - 1) - f (x - y) = f x * f y :=
suffices -(x * -y + 1) = x * y - 1,
  from case2_map_even h h0 y ▸ h x (-y) ▸ congr_arg2 _
    ((congr_arg f this.symm).trans $ case2_map_even h h0 _)
    (congr_arg f $ sub_eq_add_neg x y),
(neg_add' _ _).trans $ congr_arg2 _ ((neg_mul _ _).symm.trans $ neg_mul_neg x y) rfl

/-- (6.3) -/
lemma case2_map_sq_sub_one (h3 : f 0 = -1) (x : R) : f (x ^ 2 - 1) = f x ^ 2 - 1 :=
  (sq x).symm ▸ (eq_add_of_sub_eq $ case2_good_alt h h0 x x).trans $
    (congr_arg2 _ (sq (f x)).symm ((congr_arg f $ sub_self x).trans h3)).trans
    (sub_eq_add_neg _ _).symm 

/-- (6.4) -/
lemma case2_map_self_mul_add_one_sub_one (x : R) : f (x * (x + 1) - 1) = f x * f (x + 1) :=
  (eq_add_of_sub_eq $ case2_good_alt h h0 x (x + 1)).trans $
    add_right_eq_self.mpr $ h0 ▸ congr_arg f $ sub_add_cancel' x 1 

/-- (6.5) -/
lemma case2_map_add_two_eq (x : R) : f (x + 2) = f 2 * (f (x + 1) - f x) + f (x - 1) :=
begin
  have h1 : f (-(2 * x + 1)) = f (2 * (-(x + 1)) + 1) := congr_arg f (by ring),
  have h2 := case2_map_even h h0,
  have h3 := λ t, eq_add_of_sub_eq (h 2 t),
  rw [h2, h3, h3, h2, ← eq_sub_iff_add_eq', add_sub_right_comm, ← mul_sub] at h1,
  refine (congr_arg f $ add_comm _ _).trans (h1.trans $ congr_arg2 _ rfl _),
  rw [bit0, ← sub_eq_add_neg, add_sub_add_right_eq_sub, ← neg_sub, h2]
end

/-- Main claim -/
lemma case2_map_two_cases (h1 : f 0 = -1) :
  f 2 = -1 ∨ f 2 = 1 ∨ f 2 = 3 ∨ f 2 = 0 :=
suffices (f 2 + 1) * ((f 2 - 1) * ((f 2 - 3) * f 2)) = 0,
  from (mul_eq_zero.mp this).imp eq_neg_of_add_eq_zero_left $
    λ this, (mul_eq_zero.mp this).imp eq_of_sub_eq_zero $
    λ this, (mul_eq_zero.mp this).imp_left eq_of_sub_eq_zero,
begin
  have h2 := case2_map_sq_sub_one h h0 h1 2,
  rw [sq, two_mul, add_sub_assoc, bit0, add_sub_cancel, ← bit0] at h2,
  have h3 := case2_map_add_two_eq h h0,
  have h4 := h3 (1 + 1),
  rw [add_sub_cancel, ← bit0, good_map_one h, add_zero, h2] at h4,
  have h5 := case2_map_self_mul_add_one_sub_one h h0 2,
  rw [two_mul, add_sub_assoc, add_sub_cancel, h3, add_sub_cancel,
      add_assoc, ← bit0, h4, h2, ← sub_eq_zero] at h5,
  rw ← h5, ring
end

/-- (6.6) -/
lemma case2_special_identity (x : R) :
  f x * f (x + 1) - f (x - 1) * f (x + 2) = f x * f 2 + f (x + 2) :=
by calc
f x * f (x + 1) - f (x - 1) * f (x + 2)
  = f (x * (x + 1) - 1) - (f ((x - 1) * (x + 2) + 1) - f (x - 1 + (x + 2))) :
  congr_arg2 _ (case2_map_self_mul_add_one_sub_one h h0 x).symm (h _ _).symm
... = f (x * (x + 1) - 1) - f ((x - 1) * (x + 2) + 1) + f (x - 1 + (x + 2)) :
  (sub_add _ _ _).symm
... = 0 + f (x * 2 + 1) :
  congr_arg2 _ (sub_eq_zero_of_eq $ congr_arg f $ by ring) (congr_arg f $ by ring)
... = f x * f 2 + f (x + 2) :
   (zero_add _).trans $ eq_add_of_sub_eq (h x 2)

end step6









/- ### Step 7: Subcase 2.1: `f(-1) = 0` and `f(2) = 0 ≠ 3` -/

section step7

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

/-- If `f(2) = 0`, then `3 ∈ I` -/
lemma case2_1_lem1 (h1 : f 2 = 0) (x : R) : f (3 + x) = f x :=
  (congr_arg f $ add_rotate 2 1 x).trans $ (case2_map_add_two_eq h h0 _).trans $
    (add_sub_cancel' 1 x).symm ▸ add_left_eq_self.mpr $ mul_eq_zero_of_left h1 _


section three_eq_zero

variables (h1 : (3 : R) = 0)
include h1

/-- (7.1) -/
lemma case2_1_lem2 (x : R) : f x * f (x + 1) - f (x - 1) ^ 2 = f (x - 1) :=
  let h2 := case2_special_identity h h0 x in
  by rwa [eq_neg_of_add_eq_zero_left h1, h0,
    mul_zero, zero_add, ← sub_eq_add_neg, ← sq] at h2

/-- (7.1) with `x` replaced by `x + 1` -/
lemma case2_1_lem3 (x : R) : f (x + 1) * f (x - 1) - f x ^ 2 = f x :=
  let h2 := case2_1_lem2 h h0 h1 (x + 1) in by rwa [add_sub_cancel, add_assoc,
  ← bit0, eq_neg_of_add_eq_zero_left h1, ← sub_eq_add_neg] at h2

/-- (7.2) -/
lemma case2_1_lem4 (x : R) : f (x - 1) + f x + f (x + 1) = -1 ∨ f x = f (x - 1) :=
suffices (f (x - 1) + f x + f (x + 1) + 1) * (f x - f (x - 1)) = 0,
  from (mul_eq_zero.mp this).imp eq_neg_of_add_eq_zero_left eq_of_sub_eq_zero,
by calc _ = f x * f (x + 1) - f (x - 1) ^ 2
  - (f (x + 1) * f (x - 1) - f x ^ 2) - (f (x - 1) - f x) : by ring
... = 0 : sub_eq_zero_of_eq $ congr_arg2 has_sub.sub
  (case2_1_lem2 h h0 h1 x) (case2_1_lem3 h h0 h1 x)

/-- (7.3) -/
lemma case2_1_lem5 {c : R} (h2 : f (c + 1) = 0) (h3 : f (c - 1) = 0) : ∀ x, f (c + x) = f x :=
  let h4 : (2 : R) = -1 := eq_neg_of_add_eq_zero_left h1 in
suffices ∀ x, f ((x + 1) - (c - 1)) = f ((x + 1) + (c + 1)),
  from λ x, let h5 := this (x - (c + 1) - 1) in
    by rwa [sub_add_cancel, sub_add_cancel, sub_sub, add_add_sub_cancel,
      ← two_mul, h4, neg_one_mul, sub_neg_eq_add, add_comm] at h5,
λ x, (eq_of_sub_eq_zero $ (case2_good_alt h h0 (x + 1) (c - 1)).trans
  (mul_eq_zero_of_right _ h3)).symm.trans $
let h5 : ∀ x y : R, f y = 0 → f (x * y + 1) = f (x + y) :=
  λ x y h5, eq_of_sub_eq_zero $ (h x y).trans (mul_eq_zero_of_right _ h5) in
  by rw [← h5 _ _ h2, add_one_mul, add_sub_assoc, sub_sub, add_one_mul, add_assoc, add_assoc,
    ← bit0, h4, sub_neg_eq_add, ← sub_eq_add_neg, ← h5 _ _ h3, ← h5 _ _ h2, mul_right_comm]

end three_eq_zero


section quotient

variables (h1 : f 2 = 0) (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h3 : f 0 = -1)
include h1 h2 h3

/-- (7.4) -/
lemma case2_1_lem6 (x : R) : f (x - 1) + f x + f (x + 1) = -1 :=
begin
  have h4 := h2 3 (case2_1_lem1 h h0 h1),
  have h5 := case2_1_lem4 h h0 h4,
  refine (h5 x).elim id (λ h6, _),
  have h7 := h5 (x - 1),
  rw [sub_add_cancel, sub_sub, ← bit0, eq_neg_of_add_eq_zero_left h4, sub_neg_eq_add] at h7,
  cases h7, exact (add_rotate _ _ _).symm.trans h7,
  have h8 := case2_1_lem2 h h0 h4 x,
  rw [← h7, h6, ← sq, sub_self, eq_comm] at h8,
  have h9 := case2_1_lem5 h h0 h4 (h7.symm.trans h8) h8 0,
  rw [add_zero, h6, h8, h3, zero_eq_neg] at h9,
  exact absurd h9 one_ne_zero
end

variables (h4 : f 2 ≠ 3)
include h4

/-- (7.5) -/
lemma case2_1_lem7 (x : R) : f x = -1 ∨ f x = 0 :=
suffices 3 * ((f x + 1) * f x) = 0,
  from (mul_eq_zero.mp this).elim (λ h5, false.elim $ h4 $ h1.trans h5.symm)
    (λ this, (mul_eq_zero.mp this).imp_left eq_neg_of_add_eq_zero_left),
begin
  have h5 := case2_1_lem6 h h0 h1 h2 h3 (x ^ 2),
  rw [case2_map_sq_sub_one h h0 h3 x, add_rotate, ← add_sub_assoc, sub_eq_neg_self] at h5,
  nth_rewrite 0 ← sub_add_cancel (x ^ 2) (1 ^ 2) at h5,
  rw [sq_sub_sq, one_pow, eq_add_of_sub_eq (h _ _), sq,
      add_add_sub_cancel, eq_add_of_sub_eq (h _ _), ← two_mul] at h5,
  have h6 := h2 3 (case2_1_lem1 h h0 h1),
  rw [eq_add_of_sub_eq (case2_1_lem3 h h0 h6 x),
    eq_neg_of_add_eq_zero_left h6, neg_one_mul, case2_map_even h h0] at h5,
  rw ← h5, ring
end

/-- (7.6) -/
lemma case2_1_lem8 (x : R) (h5 : f x = -1) : x = 0 :=
begin
  replace h4 := case2_1_lem7 h h0 h1 h2 h3 h4,
  replace h3 := case2_1_lem6 h h0 h1 h2 h3 x,
  rw [h5, add_right_comm, add_left_eq_self] at h3,
  have h6 := eq_add_of_sub_eq' (case2_1_lem3 h h0 (h2 3 $ case2_1_lem1 h h0 h1) x),
  rw [sq, ← add_one_mul, mul_eq_zero_of_left (add_eq_zero_iff_eq_neg.mpr h5),
      eq_neg_of_add_eq_zero_left h3, mul_neg, neg_eq_zero, mul_self_eq_zero] at h6,
  rw [h6, add_zero] at h3,
  exact h2 x (case2_1_lem5 h h0 (h2 3 $ case2_1_lem1 h h0 h1) h6 h3)
end

/-- The main lemma for the subcase -/
lemma case2_1_lem9 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 :=
  let h5 := case2_1_lem7 h h0 h1 h2 h3 h4,
    h6 := case2_1_lem8 h h0 h1 h2 h3 h4,
    h7 := h2 3 $ case2_1_lem1 h h0 h1 in
  (h5 x).imp (h6 x) $ λ h8, (h5 (x + 1)).symm.imp
    (λ h9, eq_of_sub_eq_zero $ h2 _ $ case2_1_lem5 h h0 h7
      ((congr_arg f $ sub_add_cancel x 1).trans h8)
      (by rwa [sub_sub, ← bit0, sub_eq_add_neg, neg_eq_of_add_eq_zero_right h7]))
    (λ h9, eq_neg_of_add_eq_zero_left $ h6 (x + 1) h9)


lemma case2_1_𝔽₃_hom_bijective :
  bijective (𝔽₃.cast_hom $ h2 3 $ case2_1_lem1 h h0 h1) :=
  ⟨𝔽₃.cast_hom_injective _ (one_ne_zero_of_map_zero h h3),
  λ x, (case2_1_lem9 h h0 h1 h2 h3 h4 x).elim (λ h5, ⟨𝔽₃.𝔽₃0, h5.symm⟩) $
    λ h5, h5.elim (λ h5, ⟨𝔽₃.𝔽₃1, h5.symm⟩) (λ h5, ⟨𝔽₃.𝔽₃2, h5.symm⟩)⟩

lemma case2_1_quotient_sol :
  f = 𝔽₃_map2 S ∘
    (ring_equiv.of_bijective _ $ case2_1_𝔽₃_hom_bijective h h0 h1 h2 h3 h4).symm :=
(mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x,
match x with
| 𝔽₃.𝔽₃0 := h3
| 𝔽₃.𝔽₃1 := good_map_one h
| 𝔽₃.𝔽₃2 := h0
end

end quotient


variables (h1 : f 0 = -1) (h2 : f 2 = 0) (h3 : f 2 ≠ 3)
include h1 h2 h3

lemma case2_1_lift_decomp : ∃ φ : R ⧸ period_ideal h ≃+* 𝔽₃, period_lift h = 𝔽₃_map2 S ∘ φ :=
  ⟨_, case2_1_quotient_sol (period_lift_is_good h) h0 h2 (zero_of_periodic_period_lift h) h1 h3⟩

/-- Solution for the current subcase -/
theorem case2_1_sol : ∃ φ : R →+* 𝔽₃, surjective φ ∧ f = 𝔽₃_map2 S ∘ φ :=
  exists.elim (case2_1_lift_decomp h h0 h1 h2 h3) $
    λ ψ h4, let π := ideal.quotient.mk (period_ideal h) in
    ⟨ψ.to_ring_hom.comp π, ψ.surjective.comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h4⟩

end step7









/- ### Step 8: Subcase 2.2: `f(-1) = 0` and `f(2) = 1 ≠ -1` -/

section step8

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 1)
include h h0 h1

/-- (8.1) -/
lemma case2_2_lem1 (x : R) : f (x + 2) + f x = f (x + 1) + f (x - 1) :=
  by rw [case2_map_add_two_eq h h0 x, h1, one_mul, add_assoc, sub_add_add_cancel]

/-- `4 ∈ I` -/
lemma case2_2_lem2 (x : R) : f (4 + x) = f x :=
begin
  have h2 := case2_2_lem1 h h0 h1,
  have h3 := (h2 (x + 1 + 1)).symm,
  rw [add_sub_cancel, add_assoc, ← bit0, h2, add_sub_cancel, add_comm] at h3,
  refine ((add_left_injective _ h3).trans $ congr_arg f _).symm,
  rw [add_assoc x, ← bit0, add_assoc, ← bit0, add_comm]
end

variables (h2 : f 2 ≠ -1)
include h2

lemma case2_2_lem3 (x : R) : f (2 * x + 1) = 0 :=
begin
  have h3 := eq_add_of_sub_eq' (h x 2),
  rw [h1, mul_one, case2_2_lem1 h h0 h1] at h3,
  have h4 := eq_add_of_sub_eq' (h (x - 1) 2),
  rw [h1, mul_one, bit0, sub_add_add_cancel, ← h3, ← bit0] at h4,
  have h5 := eq_add_of_sub_eq (case2_good_alt h h0 (x * 2 + 1) 2),
  rw [h1, mul_one, add_sub_right_comm, ← sub_one_mul, h4, add_one_mul, add_sub_assoc,
      bit0, add_sub_cancel, ← bit0, mul_rotate, two_mul, ← bit0, mul_comm x 2,
      period_imp_quasi_period h (case2_2_lem2 h h0 h1), ← two_mul, zero_eq_mul] at h5,
  exact h5.resolve_left (λ h5, h2 $ h1.trans $ eq_neg_of_add_eq_zero_left h5)
end

lemma case2_2_lem4 : f 0 = -1 :=
  not.imp_symm (eq_zero_of_map_zero_ne_neg_one h) $
    λ h3, one_ne_zero' S $ h1.symm.trans $ congr_fun h3 2

/-- The main lemma for the subcase -/
lemma case2_2_lem5 (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (x : R) :
  (x = 0 ∨ x = 2) ∨ (x = 1 ∨ x = -1) :=
suffices (x = 0 ∨ x = 2) ∨ (x = 1 ∨ x = 2 + 1),
  from this.imp_right $ or.imp_right $ λ this, this.trans $
    eq_neg_of_add_eq_zero_left $ (add_assoc _ _ _).trans $ h3 _ $ case2_2_lem2 h h0 h1,
let h4 : f 0 = -1 := case2_2_lem4 h h0 h1 h2 in
cases_of_nonperiod_quasi_period h h3 h4 (case2_2_lem3 h h0 h1 h2)
  (λ h5, h2 $ (congr_arg f h5).trans h4) x


lemma case2_2_ℤ₄_hom_bijective (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) :
  bijective (ℤ₄.cast_hom $ h3 4 $ case2_2_lem2 h h0 h1) :=
  ⟨ℤ₄.cast_hom_injective _ (λ h4, h2 $ (congr_arg f h4).trans $ case2_2_lem4 h h0 h1 h2),
  λ x, (case2_2_lem5 h h0 h1 h2 h3 x).elim
    (λ h5, h5.elim (λ h5, ⟨ℤ₄.ℤ₄0, h5.symm⟩) (λ h5, ⟨ℤ₄.ℤ₄2, h5.symm⟩))
    (λ h5, h5.elim (λ h5, ⟨ℤ₄.ℤ₄1, h5.symm⟩) (λ h5, ⟨ℤ₄.ℤ₄3, h5.symm⟩))⟩

lemma case2_2_quotient_sol (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) :
  f = ℤ₄_map S ∘
    (ring_equiv.of_bijective _ $ case2_2_ℤ₄_hom_bijective h h0 h1 h2 h3).symm :=
(mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x,
match x with
| ℤ₄.ℤ₄0 := case2_2_lem4 h h0 h1 h2
| ℤ₄.ℤ₄1 := good_map_one h
| ℤ₄.ℤ₄2 := h1
| ℤ₄.ℤ₄3 := h0
end

lemma case2_2_lift_decomp :
  ∃ φ : R ⧸ period_ideal h ≃+* ℤ₄, period_lift h = ℤ₄_map S ∘ φ :=
  ⟨_, case2_2_quotient_sol (period_lift_is_good h) h0 h1 h2 (zero_of_periodic_period_lift h)⟩

/-- Solution for the current subcase -/
theorem case2_2_sol : ∃ φ : R →+* ℤ₄, surjective φ ∧ f = ℤ₄_map S ∘ φ :=
  exists.elim (case2_2_lift_decomp h h0 h1 h2) $
    λ ψ h3, let π := ideal.quotient.mk (period_ideal h) in
    ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h3⟩

end step8









/- ### Step 9: Subcase 2.3: `f(-1) = 0` and `f(2) = 3 ≠ 1` -/

section step9_domain

variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

/-- A copy of `case2_1_lem6` (7.4) from Subcase 2.1,
  without quotienting by the "period ideal". -/
lemma case2_1_lem6_nonquotient (h1 : f 2 = 0) (h2 : f 0 = -1) (x : R) :
  f (x - 1) + f x + f (x + 1) = -1 :=
  let X := case2_1_lem6 (period_lift_is_good h) h0 h1
    (zero_of_periodic_period_lift h) h2 (ideal.quotient.mk _ x) in X

variables (h1 : f 2 = 3)
include h1

/-- (9.1) -/
lemma case2_3_lem1 (x : R) : f (x + 2) = 3 * (f (x + 1) - f x) + f (x - 1) :=
  h1 ▸ case2_map_add_two_eq h h0 x

/-- (9.2) -/
lemma case2_3_lem2 (x : R) :
  f x * (3 * f (x - 1) + f (x + 1)) - (f (x - 1) + 3 * f (x + 1)) * (1 + f (x - 1)) = 0 :=
begin
  have h2 := sub_eq_zero_of_eq (case2_special_identity h h0 x),
  rw [h1, case2_3_lem1 h h0 h1] at h2,
  rw ← h2, ring
end

/-- (9.3) -/
lemma case2_3_lem3 (x : R) :
  f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x + 1) = f (x - 1) :=
suffices (f (x + 1) + f (x - 1) - (2 * f x + 2)) * (f (x + 1) - f (x - 1)) = 0,
  from (mul_eq_zero.mp this).imp eq_of_sub_eq_zero eq_of_sub_eq_zero,
begin
  have X := case2_map_even h h0,
  have X0 := case2_3_lem2 h h0 h1,
  have h2 := case2_3_lem2 h h0 h1 (-x),
  rw [X, ← neg_add', X, neg_add_eq_sub, ← neg_sub x, X] at h2,
  refine eq.trans _ ((congr_arg2 has_sub.sub (X0 x) h2).trans $ sub_zero _),
  ring
end

/-- (9.4) -/
lemma case2_3_lem4 (h2 : f 2 ≠ 1) (x : R) :
  f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ (f (x + 1) = 0 ∧ f (x - 1) = 0) :=
let X := case2_3_lem3 h h0 h1 in (X x).imp_right $ λ h3,
  suffices f (x - 1) = 0, from ⟨h3.trans this, this⟩,
begin
  have h4 := case2_3_lem2 h h0 h1 x,
  rw [h3, sub_eq_zero, add_comm, ← one_add_mul, mul_comm,
      mul_eq_mul_left_iff, mul_eq_zero, bit1, add_left_comm] at h4,
  have h5 : (2 : S) + 2 ≠ 0 :=
    by rw [← two_mul, mul_self_ne_zero]; exact add_left_ne_self.mp (h1.symm.trans_ne h2),
  revert h4; suffices : f x ≠ 1 + f (x - 1),
    exact λ h4, (h4.resolve_left this).resolve_left h5,
  
  intros h4,
  have h6 := case2_3_lem1 h h0 h1 x,
  rw [h3, ← sub_eq_of_eq_add' h4, sub_sub_cancel_left, mul_neg_one,
      neg_add_eq_sub, sub_sub, bit1, add_left_comm, ← bit0] at h6,
  have h7 := X (x + 1),
  rw [add_sub_cancel, add_assoc, ← bit0, h6] at h7,
  refine h5 (h7.elim (λ h7, _) sub_eq_self.mp),
  rwa [← add_sub_right_comm, h3, ← two_mul, ← mul_add_one,
       ← h4.trans (add_comm _ _), sub_eq_self] at h7
end

/-- (9.5) -/
lemma case2_3_lem5 (h2 : f 2 ≠ 1) (x : R) :
  f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ (f x = 0 ∧ f (x + 1) = 0 ∧ f (x - 1) = 0) :=
  let X := case2_3_lem4 h h0 h1 h2 in (X x).elim or.inl $ λ h3, (X (x + 1)).imp
    (λ h4, eq_add_of_sub_eq' $ (eq_of_sub_eq_zero $ by rw [add_sub_cancel, add_assoc,
      ← bit0, case2_3_lem1 h h0 h1]; ring).symm.trans $ sub_eq_of_eq_add' h4)
    (λ h4, ⟨add_sub_cancel x 1 ▸ h4.2, h3⟩)

/-- (9.6) Very slow, but... well it works -/
lemma case2_3_lem6 (h2 : f 2 ≠ 1) (h3 : f 0 = -1) (x : R) :
  f (x + 1) + f (x - 1) = 2 * f x + 2 :=
let X := case2_3_lem5 h h0 h1 h2 in (X x).resolve_right $ λ h4, (em $ f 2 = 0).elim
---- Case 1: `char(S) = 3` (borrows case2_1_lem6 i.e. (7.4) from Subcase 2.1)
(λ h5, absurd (case2_1_lem6_nonquotient h h0 h5 h3 x) $
  by rw [h4.1, h4.2.1, h4.2.2, add_zero, add_zero, zero_eq_neg]; exact one_ne_zero' S)
---- Case 2: `char(S) ≠ 3`
(λ h5, let X0 := add_left_ne_self.mp (h1.symm.trans_ne h2) in suffices f (2 * x) = -3,
---- First reduce to `f(2x) = -3`
from (X (2 * x)).symm.elim
  (λ h6, absurd (this.symm.trans h6.1) $ neg_ne_zero.mpr $ h1.symm.trans_ne h5)
  (λ h6, begin
    have h7 := eq_add_of_sub_eq (h 2 (x - 1)),
    rw [h4.2.2, mul_zero, zero_add, mul_sub_one, bit0, add_add_sub_cancel,
        ← sub_sub, sub_add_cancel, ← bit0, add_comm, h4.2.1] at h7,
    have h8 := eq_add_of_sub_eq (case2_good_alt h h0 (x + 1) 2),
    rw [h4.2.1, zero_mul, zero_add, bit0, add_sub_add_right_eq_sub, add_one_mul,
        ← add_assoc, add_sub_cancel, ← bit0, mul_comm, h4.2.2] at h8,
    rw [h7, h8, add_zero, this, ← mul_add_one, bit1, neg_add,
        neg_add_cancel_right, mul_neg, zero_eq_neg, mul_self_eq_zero] at h6,
    exact X0 h6
  end),
---- Now prove that `f(2x) = -3`
suffices 2 * (f (2 * x) + 3) = 0,
  from eq_neg_of_add_eq_zero_left $ (mul_eq_zero.mp this).resolve_left X0,
begin
  have h6 := eq_add_of_sub_eq (case2_good_alt h h0 (x + 1) (x - 1)),
  rw [← sq_sub_sq, one_pow, add_sub_sub_cancel,
      h4.2.1, zero_mul, zero_add, ← bit0, h1] at h6,
  have h7 := eq_add_of_sub_eq (case2_good_alt h h0 x x),
  rw [← sq, h4.1, zero_mul, zero_add, sub_self, h3] at h7,
  have h8 := eq_add_of_sub_eq (h (x + 1) (x - 1)),
  rw [← sq_sub_sq, one_pow, h4.2.1, zero_mul, zero_add, add_add_sub_cancel] at h8,
  have h9 := case2_3_lem1 h h0 h1 (x ^ 2 - 1),
  rw [h8, h7, h6, sq, bit0, sub_add_add_cancel, eq_add_of_sub_eq (h x x),
      h4.1, zero_mul, zero_add, ← two_mul, eq_comm, ← sub_eq_zero] at h9,
  rw ← h9, ring
end)

end step9_domain



section step9_field

variables {R S : Type*} [comm_ring R] [field S]

def hom_guess (f : R → S) (x : R) := (f x - f (x - 1) + 1) / 2

variables {f : R → S} (h : good f) (h0 : f (-1) = 0)
  (h1 : f 2 = 3) (h2 : f 2 ≠ 1) (h3 : f 0 = -1)
include h h0 h1 h2 h3

/-- (9.g1) -/
lemma case2_3_lem_g1 : hom_guess f 0 = 0 :=
  div_eq_zero_iff.mpr $ or.inl $ by rw [h3, zero_sub, h0, sub_zero, neg_add_self]

/-- (9.g2) -/
lemma case2_3_lem_g2 (x : R) : hom_guess f (x + 1) = hom_guess f x + 1 :=
  let X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2) in
  by rw [hom_guess, hom_guess, div_eq_iff X, add_one_mul, div_mul_cancel _ X, add_right_comm,
    add_left_inj, add_sub_cancel, sub_eq_iff_eq_add', ← add_sub_right_comm, ← add_sub_assoc,
    eq_sub_iff_add_eq, ← add_assoc, ← two_mul]; exact case2_3_lem6 h h0 h1 h2 h3 x

/-- Variant of (9.g2) -/
lemma case2_3_lem_g2' (x : R) : hom_guess f (x - 1) = hom_guess f x - 1 :=
  eq_sub_of_add_eq $ (case2_3_lem_g2 h h0 h1 h2 h3 _).symm.trans $
    congr_arg _ $ sub_add_cancel x 1

/-- (9.g3) -/
lemma case2_3_lem_g3 (x : R) : hom_guess f (-x) = -hom_guess f x :=
suffices f (-x) - f (-x - 1) + 1 = -(f x - f (x - 1) + 1),
  from (congr_arg (/ (2 : S)) this).trans $ neg_div _ _,
let X := case2_map_even h h0 in by rw [X, ← neg_add', X, eq_neg_iff_add_eq_zero,
  add_add_add_comm, sub_add_sub_comm, ← two_mul, ← bit0, ← add_sub_right_comm, sub_eq_zero];
  exact (case2_3_lem6 h h0 h1 h2 h3 x).symm

/-- (9.g4) -/
lemma case2_3_lem_g4 (x : R) : f x = hom_guess f x ^ 2 - 1 :=
begin
  have X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2),
  have X0 : (2 : S) ^ 2 ≠ 0 := pow_ne_zero 2 X,
  rw [hom_guess, div_pow, div_sub_one X0, eq_div_iff X0],
  refine mul_left_cancel₀ X (eq_of_sub_eq_zero _).symm,
  rw [← case2_3_lem2 h h0 h1 x, eq_sub_of_add_eq (case2_3_lem6 h h0 h1 h2 h3 x)],
  ring
end

/-- (9.g5) -/
lemma case2_3_lem_g5 (x y : R) :
  (hom_guess f (x * y) + 1) ^ 2 - hom_guess f (x + y) ^ 2 =
    (hom_guess f x ^ 2 - 1) * (hom_guess f y ^ 2 - 1) :=
  let h4 := case2_3_lem_g4 h h0 h1 h2 h3, h5 := h x y in
    by rwa [h4, h4, h4, h4, sub_sub_sub_cancel_right, case2_3_lem_g2 h h0 h1 h2 h3] at h5

/-- (9.g6) -/
lemma case2_3_lem_g6 (x y : R) :
  (hom_guess f (x * y) - 1) ^ 2 - hom_guess f (x - y) ^ 2 =
    (hom_guess f x ^ 2 - 1) * (hom_guess f y ^ 2 - 1) :=
  let h4 := case2_3_lem_g4 h h0 h1 h2 h3, h5 := case2_good_alt h h0 x y in
    by rwa [h4, h4, h4, h4, sub_sub_sub_cancel_right, case2_3_lem_g2' h h0 h1 h2 h3] at h5

/-- (9.g7) -/
lemma case2_3_lem_g7 (x y : R) :
  2 ^ 2 * hom_guess f (x * y) = hom_guess f (x + y) ^ 2 - hom_guess f (x - y) ^ 2 :=
by calc
_ = (hom_guess f (x * y) + 1) ^ 2 - (hom_guess f (x * y) - 1) ^ 2 : by ring
... = hom_guess f (x + y) ^ 2 - hom_guess f (x - y) ^ 2 : sub_eq_sub_iff_sub_eq_sub.mp $
  (case2_3_lem_g5 h h0 h1 h2 h3 x y).trans (case2_3_lem_g6 h h0 h1 h2 h3 x y).symm

/-- (9.g8) -/
lemma case2_3_lem_g8 (x y : R) :
  (hom_guess f (x + y) ^ 2 - hom_guess f (x - y) ^ 2) ^ 2 + 2 ^ 4
    = 2 ^ 3 * (hom_guess f (x + y) ^ 2 + hom_guess f (x - y) ^ 2)
      + (2 ^ 2) ^ 2 * ((hom_guess f x ^ 2 - 1) * (hom_guess f y ^ 2 - 1)) :=
  by rw [← case2_3_lem_g5 h h0 h1 h2 h3, mul_sub, ← mul_pow,
    mul_add_one, case2_3_lem_g7 h h0 h1 h2 h3]; ring

lemma case2_3_lem_g9 (x y : R) :
  hom_guess f (x + y) + hom_guess f (x - y) = 2 * hom_guess f x
  ∨ hom_guess f (x + y) + hom_guess f (x - y) = -(2 * hom_guess f x) :=
let X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2) in
  sq_eq_sq_iff_eq_or_eq_neg.mp $ mul_left_cancel₀ (pow_ne_zero 3 X) $
begin
  have h4 := case2_3_lem_g2 h h0 h1 h2 h3,
  have h5 := case2_3_lem_g2' h h0 h1 h2 h3,
  have h6 := case2_3_lem_g8 h h0 h1 h2 h3 x,
  have h7 := congr_arg2 has_sub.sub (congr_arg2 has_add.add (h6 (y + 1)) (h6 (y - 1)))
    (congr_arg (has_mul.mul (2 : S)) (h6 y)),
  rw [← add_assoc x, h4, ← sub_sub x, h5, ← add_sub_assoc x, h5, ← sub_add x, h4, h4, h5] at h7,
  rw [← sub_eq_zero, ← sub_eq_zero_of_eq h7],
  ring
end

/-- (9.g9) -/
lemma case2_3_lem_g10 (x y : R) :
  hom_guess f (x + y) + hom_guess f (x - y) = 2 * hom_guess f x :=
  let X := case2_3_lem_g9 h h0 h1 h2 h3 in (X x y).elim id $ λ h4,
begin
  have X0 := case2_3_lem_g2 h h0 h1 h2 h3,
  have h5 := X (x + 1) y,
  rw [add_right_comm, X0, add_sub_right_comm, X0,
      add_add_add_comm, X0, mul_add_one, ← bit0] at h5,
  cases h5, exact add_left_injective _ h5,
  rw [h4, neg_add, add_right_inj, eq_neg_iff_add_eq_zero, ← two_mul, mul_self_eq_zero] at h5,
  exact absurd h5 (add_left_ne_self.mp $ h1.symm.trans_ne h2)
end

lemma case2_3_lem_g_mul (x y : R) :
  hom_guess f (x * y) = hom_guess f x * hom_guess f y :=
  mul_left_cancel₀ (pow_ne_zero 2 $ add_left_ne_self.mp $ h1.symm.trans_ne h2) $
    let h4 := case2_3_lem_g10 h h0 h1 h2 h3 in
  by rw [case2_3_lem_g7 h h0 h1 h2 h3, sq_sub_sq, h4, ← neg_sub y x, sq,
    case2_3_lem_g3 h h0 h1 h2 h3, sub_neg_eq_add, add_comm x y, h4, mul_mul_mul_comm]

lemma case2_3_lem_g_one : hom_guess f 1 = 1 :=
  by rw [← zero_add (1 : R), case2_3_lem_g2 h h0 h1 h2 h3,
    case2_3_lem_g1 h h0 h1 h2 h3, zero_add]

lemma case2_3_lem_g_add (x y : R) :
  hom_guess f (x + y) = hom_guess f x + hom_guess f y :=
begin
  have h4 := case2_3_lem_g_mul h h0 h1 h2 h3 2,
  rw [bit0, case2_3_lem_g2 h h0 h1 h2 h3,
      case2_3_lem_g_one h h0 h1 h2 h3, ← bit0, ← bit0] at h4,
  have h5 := case2_3_lem_g10 h h0 h1 h2 h3 (x + y) (x - y),
  rw [add_add_sub_cancel, ← two_mul, h4, add_sub_sub_cancel, ← two_mul, h4, ← mul_add] at h5,
  exact mul_left_cancel₀ (add_left_ne_self.mp $ h1.symm.trans_ne h2) h5.symm,
end

/-- Solution for the current subcase -/
theorem case2_3_sol : ∃ φ : R →+* S, f = λ x, φ x ^ 2 - 1 :=
⟨⟨hom_guess f,
  case2_3_lem_g_one h h0 h1 h2 h3,
  case2_3_lem_g_mul h h0 h1 h2 h3,
  case2_3_lem_g1 h h0 h1 h2 h3,
  case2_3_lem_g_add h h0 h1 h2 h3⟩,
funext $ case2_3_lem_g4 h h0 h1 h2 h3⟩

end step9_field







/- ### Step 10: Subcase 2.3: `f(-1) = 0` and `f(2) = -1` -/

section step10

namespace char2

variables {R : Type*} [comm_ring R] (h : (2 : R) = 0)
include h

lemma add_self (x : R) : x + x = 0 :=
  (two_mul x).symm.trans (mul_eq_zero_of_left h x)

lemma add_add_cancel (x y : R) : x + y + y = x :=
  (add_assoc x y y).trans $ (congr_arg (has_add.add x) (add_self h y)).trans (add_zero x)

lemma sub_eq_add (x y : R) : x - y = x + y :=
  sub_eq_of_eq_add (add_add_cancel h x y).symm

lemma add_add_left_cancel (x y : R) : x + (x + y) = y :=
  (add_assoc x x y).symm.trans $ (congr_arg (+ y) (add_self h x)).trans (zero_add y)

lemma add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  (add_sq' x y).trans $ (congr_arg (has_add.add _) $
    mul_eq_zero_of_left (mul_eq_zero_of_left h x) y).trans (add_zero _)

lemma add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 :=
  (add_sq h x 1).trans $ congr_arg (has_add.add $ x ^ 2) (one_pow 2)

lemma add_eq_iff_eq_add {x y z : R} : x + y = z ↔ x = z + y :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add

lemma add_eq_iff_eq_add' {x y z : R} : x + y = z ↔ x = y + z :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add'

lemma add_eq_zero_iff_eq {x y : R} : x + y = 0 ↔ x = y :=
  (add_eq_iff_eq_add h).trans $ by rw zero_add

lemma add_pow_four (x y : R) : (x + y) ^ 4 = x ^ 4 + y ^ 4 :=
  by rw [bit0, ← two_mul, pow_mul, pow_mul, pow_mul, add_sq h, add_sq h]

lemma add_one_pow_four (x : R) : (x + 1) ^ 4 = x ^ 4 + 1 :=
  (add_pow_four h x 1).trans $ congr_arg (has_add.add $ x ^ 4) (one_pow 4)

end char2



variables {R S : Type*} [comm_ring R] [comm_ring S] [is_domain S] {f : R → S} (h : good f)
include h

/-- `2 ∈ I` -/
lemma case2_4_lem1 (h0 : f (-1) = 0) (h1 : f 2 = -1) : ∀ x, f (2 + x) = f x :=
suffices ∀ x, f (x + 1) = f (x - 1),
  from λ x, add_rotate x 1 1 ▸ (this (x + 1)).trans $ congr_arg f (add_sub_cancel x 1), 
---- First assume an intermediate statement
suffices ∀ x, f (x + 1) = f (x - 1) ∨ f x + f (x - 1) = -1,
from λ x, (this x).elim id $ λ h2, begin
  have h3 := this (-x),
  have h4 := case2_map_even h h0,
  rw [h4, neg_add_eq_sub, ← neg_sub, h4, ← neg_add', h4] at h3,
  exact h3.elim eq.symm (λ h3, add_right_injective (f x) $ h3.trans h2.symm)
end,
---- Now prove the intermediate statement
λ x, suffices (f (x + 1) - f (x - 1)) * (f x + f (x - 1) + 1) = 0,
  from (mul_eq_zero.mp this).imp eq_of_sub_eq_zero eq_neg_of_add_eq_zero_left,
by rw [← sub_eq_zero_of_eq (case2_special_identity h h0 x),
  case2_map_add_two_eq h h0 x, h1]; ring



section Rchar2

variables (h0 : (2 : R) = 0)
include h0

lemma case2_4_lem2 : f (-1) = 0 :=
  eq_neg_of_add_eq_zero_left h0 ▸ good_map_one h

/-- (10.1) -/
lemma case2_4_lem3 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  (congr_arg f (char2.sub_eq_add h0 _ _).symm).trans $
    case2_map_self_mul_add_one_sub_one h (case2_4_lem2 h h0) x

variables (h1 : f 0 = -1)
include h1

/-- (10.2) -/
lemma case2_4_lem4 (x : R) : f (x ^ 2 + 1) = f x ^ 2 - 1 :=
  (congr_arg f (char2.sub_eq_add h0 _ _).symm).trans $
    case2_map_sq_sub_one h (case2_4_lem2 h h0) h1 x

/-- (10.3) -/
lemma case2_4_lem5 (x : R) : f (x ^ 2) = f (x + 1) ^ 2 - 1 :=
  (congr_arg f ((congr_arg2 _ (char2.add_one_sq h0 x) rfl).trans $
    char2.add_add_cancel h0 _ 1).symm).trans $
    case2_4_lem4 h h0 h1 (x + 1)

lemma case2_4_lem6 : ∀ x, f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 :=
let h3 := case2_4_lem3 h h0, h4 := case2_4_lem5 h h0 h1 in
---- (10.L1.1)
have h5 : ∀ x, (f (x + 1) ^ 2 - 1) * (f (x + 1) - 1) + f x * f (x + 1) = f x * f (x * (x + 1)) :=
λ x, by rw [← h3, ← h4, ← h, eq_sub_iff_add_eq, add_right_comm,
  ← eq_sub_iff_add_eq, ← mul_assoc, mul_add_one, ← sq, add_left_comm,
  char2.add_self h0, add_zero, ← mul_add_one, sub_add_cancel, add_assoc, h],
---- Assuming the lemma + possibility of `f(x + 1) = f(x)`
λ x, suffices (f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1) ∨ f x = f (x + 1),
  from this.elim id $ λ h6, or.inr $
begin
  rw [← h6, ← two_mul, eq_comm],
  have h7 := case2_4_lem4 h h0 h1,
  have h8 := h7 (x * (x + 1)),
  rw [mul_pow, char2.add_one_sq h0, h3, h4, h7] at h8,
  replace h8 := sub_eq_zero_of_eq (congr_arg2 has_mul.mul (rfl : (f x) ^ 2 = (f x) ^ 2) h8),
  rw [mul_sub_one ((f x) ^ 2), ← mul_pow, ← h5, ← h6] at h8,
  replace h8 : (1 - 2 * f x) * (f x ^ 2 - 1) = 0 := h8 ▸ by ring,
  rw mul_eq_zero at h8, refine h8.elim eq_of_sub_eq_zero (λ h8, _),
  refine absurd (h5 (x ^ 2)) _,
  rw [h7, h4, ← h6, h8, sq, zero_mul, zero_mul, add_zero, zero_sub, ← sq, neg_one_sq],
  exact one_ne_zero' S
end,
---- Proving the lemma + possibility of `f(x + 1) = f(x)`
suffices (f x ^ 2 + f (x + 1) ^ 2 - 1) * (f x + f (x + 1) - 1) * (f x - f (x + 1)) = 0,
  from (mul_eq_zero.mp this).imp (λ this, (mul_eq_zero.mp this).imp
    eq_of_sub_eq_zero eq_of_sub_eq_zero) eq_of_sub_eq_zero,
begin
  have h6 := congr_arg (has_mul.mul $ f x) (h5 (x + 1)),
  rw [char2.add_add_cancel h0, mul_left_comm, mul_comm (x + 1), ← h5] at h6,
  rw ← sub_eq_zero_of_eq h6, ring
end



lemma case2_4_quotient_sol1 (h3 : (2 : S) = 0) :
  ∃ φ : R →+* S, f = λ x, φ x - 1 :=
  eq_hom_sub_one_of h h1 $ λ x y,
begin
  ---- (10.L2.1)
  have h4 : ∀ x, f (x + 1) = f x + 1 :=
  λ x, (char2.add_eq_iff_eq_add' h3).mp $ (add_comm _ _).trans $
    (case2_4_lem6 h h0 h1 x).symm.elim id $
    λ h4, (sq_eq_one_iff.mp $ (char2.add_sq h3 _ _).trans h4).elim id $
    λ h5, h5.trans $ neg_eq_of_add_eq_zero_left h3,
  ---- (10.L2.2)
  have h5 : ∀ x y, f (x * y) = f x * f y + f (x + y) + 1 :=
    λ x y, (char2.add_eq_iff_eq_add h3).mp
      ((h4 _).symm.trans $ eq_add_of_sub_eq $ h x y),
  ---- Back to the main equality
  let a := f x, let b := f y, let c := f (x + y),
  have h6 := h5 (x * y) ((y + 1) * (x + 1)),
  rw [mul_mul_mul_comm, h5, add_left_inj] at h6,
  have h7 : x * y + (y + 1) * (x + 1) = x * (y + 1) + y * (x + 1) + 1 := by ring,
  rw [h7, h4, ← add_assoc, ← sub_eq_iff_eq_add', add_sub_add_right_eq_sub] at h6,
  replace h7 : f (x * y) = a * b + c + 1 := h5 x y,
  have h8 : f (x * (y + 1)) = a * (b + 1) + (c + 1) + 1 :=
    by rw [h5, ← add_assoc, h4, h4],
  have h9 : f (y * (x + 1)) = b * (a + 1) + (c + 1) + 1 :=
    by rw [h5, add_left_comm, ← add_assoc, h4, h4],
  have h10 : f ((y + 1) * (x + 1)) = (b + 1) * (a + 1) + c + 1 :=
    by rw [h5, add_add_add_comm, ← bit0, h0, add_zero, add_comm y x, h4, h4],
  replace h6 := (congr_arg2 _ (congr_arg2 _ h8 h9) (congr_arg2 _ h7 h10)).symm.trans h6,
  rw [← sub_eq_iff_eq_add', ← h6, eq_comm, ← sub_eq_zero],
  refine eq.trans _ (mul_eq_zero_of_left h3 $ (a + 1) * (b + 1)),
  ring
end



variables (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h3 : (2 : S) ≠ 0)
include h2 h3

lemma case2_4_lem7 (x : R) :
  f x * f (x + 1) = 0 ∨ (f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1) :=
---- Reduce the condition to `2 f(x)^2 f(x + 1)^2 (f(x)^2 + f(x + 1)^2 - 3) = 0`
suffices 2 * (f x * f (x + 1)) ^ 2 * (f x ^ 2 + f (x + 1) ^ 2 - 3) = 0,
  from (mul_eq_zero.mp this).imp
    (λ h4, sq_eq_zero_iff.mp $ (mul_eq_zero.mp h4).resolve_left h3)
    (λ h4, let h5 := eq_of_sub_eq_zero h4,
      h6 := (case2_4_lem6 h h0 h1 x).resolve_left $
        (eq_of_sub_eq_zero h4).trans_ne $ add_left_ne_self.mpr h3 in
      ⟨h6, let h7 := add_sq' (f x) (f (x + 1)) in
        by rwa [h5, h6, one_pow, bit1, add_right_comm, self_eq_add_left, mul_assoc,
          ← mul_one_add, mul_eq_zero, or_iff_right h3, add_eq_zero_iff_neg_eq, eq_comm] at h7⟩),
---- Prove the above equality
begin
  have h4 : ∀ x, f (x ^ 4) = (f x ^ 2 - 1) ^ 2 - 1 :=
    λ x, by rw [bit0, ← two_mul, pow_mul, case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1],
  have h5 := case2_4_lem3 h h0,
  have h6 := char2.add_one_pow_four h0,
  have h7 := h4 (x * (x + 1) + 1),
  rw [h5, h6, mul_pow, h6, h5, h4, ← h6, h4, eq_comm, ← sub_eq_zero] at h7,
  rw ← h7, ring
end

/-- This lemma's proof implementation is too slow... at least 0.7s.
  It should be optimized or broken down into more lemmas.
  Or, you could give a simpler proof. -/
lemma case2_4_lem8 (c : R) (h4 : f c = -1) : c = 0 :=
---- (10.L3.1)
have h5 : ∀ x, f x = -1 → f (x + 1) = 0 :=
  λ x h5, let X : (1 : S) ≠ 0 := one_ne_zero' S in (case2_4_lem7 h h0 h1 h2 h3 x).elim
    (λ h6, (mul_eq_zero.mp h6).resolve_left $ h5.trans_ne $ neg_ne_zero.mpr X)
    (λ h6, by rw [h5, neg_one_mul, neg_inj, neg_add_eq_iff_eq_add] at h6;
      exact absurd (h6.1.symm.trans h6.2) (add_right_ne_self.mpr X)),
---- (10.L3.2)
have h6 : ∀ c, f c = -1 → ∀ x, f (c ^ 2 + c * x + 1) = -f (c * x + 1) :=
λ c h6 x, by rw [eq_add_of_sub_eq (h c _), sq, ← mul_add,
  eq_add_of_sub_eq (h c _), h6, ← add_assoc, char2.add_self h0, zero_add]; ring,
---- The main problem
begin
  have X := char2.add_sq h0,
  have X0 := case2_4_lem5 h h0 h1,

  -- Reduce to `c^4 = 0`
  have h7 := X0 c,
  rw [h5 c h4, zero_pow (nat.succ_pos 1), zero_sub] at h7,
  suffices h8 : (c ^ 2) ^ 2 = 0,
  { suffices h9 : ∀ c, f c = -1 → c ^ 2 = 0 → c = 0,
      exact h9 c h4 (h9 _ h7 h8),
    intros d h9 h10,
    refine h2 d ((period_iff h).mpr ⟨(quasi_period_iff h).mpr $ λ x, _, h9.trans h1.symm⟩),
    have h11 := h6 d h9 x,
    rw [h10, zero_add, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h11,
    exact h11.resolve_left h3 },
  
  -- Get `c^6 + c^4 = 0`
  have h8 : ∀ x, f ((c ^ 2) ^ 2 + c ^ 2 + c ^ 2 * x + 1) = f (c ^ 2 * x + 1) :=
    λ x, by rw [add_assoc ((c ^ 2) ^ 2), ← mul_one_add, h6 _ h7, 
      mul_one_add, sq, mul_assoc, ← sq, h6 _ h4, neg_neg],
  have h9 : f (c + 1) = 0 := h5 c h4,
  have h10 : f (c ^ 2 + c + 1) = 0 :=
    by rw [sq, ← mul_add_one, case2_4_lem3 h h0, h9, mul_zero],
  replace h8 : ∀ x, f (((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 * x + 1) = 0 :=
    suffices f ((c ^ 2) ^ 2 + c ^ 2) = -1, from λ x,
      by rw [mul_assoc, mul_left_comm, ← h8, mul_left_comm, ← mul_one_add, add_comm (1 : R),
        eq_add_of_sub_eq (h _ _), this, neg_one_mul, ← add_assoc, h8, neg_add_self],
    by rw [← X, X0, h10, sq, zero_mul, zero_sub],
  replace h8 : ((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 = 0 :=
    h2 _ ((period_iff h).mpr ⟨(quasi_period_iff h).mpr h8,
      by rwa [← X, ← mul_pow, X0, h1, sub_eq_neg_self, sq_eq_zero_iff, sq, ← add_one_mul,
        mul_rotate, ← sq, eq_add_of_sub_eq (h _ _), h9, mul_zero, zero_add, ← add_assoc]⟩),

  -- Now show that `c^4 = 0`
  refine h2 _ ((period_iff h).mpr ⟨(quasi_period_iff h).mpr $ λ x, _,
    by rw [X0, h1, sub_eq_neg_self, sq_eq_zero_iff]; exact h5 _ h7⟩),
  rw [sq, ← add_one_mul, mul_assoc, ← sq] at h8,
  have h11 := eq_add_of_sub_eq (h (c ^ 2 + 1) ((c ^ 2) ^ 2 * x + 1)),
  rw [h5 _ h7, zero_mul, zero_add, mul_add_one, ← mul_assoc, h8, zero_mul, zero_add,
      add_left_comm, char2.add_add_cancel h0, h7, eq_comm] at h11,
  rw [sq, sq, mul_assoc, mul_assoc, ← neg_eq_zero, ← h6 _ h4,
      ← mul_assoc, ← sq, ← mul_assoc, ← sq, add_comm (c ^ 2)],
  exact h5 _ h11
end

lemma case2_4_lem9 (x : R) :
  (x ^ 2 = 0 ∨ x ^ 2 = 1) ∨ (f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0) :=
---- Reduce to showing that either `f(x) = 0`, `f(x + 1) = 0`, or `f(x)^2 + f(x + 1)^2 = 3`
suffices (f (x + 1) = 0 ∨ f x = 0) ∨ f x ^ 2 + f (x + 1) ^ 2 = 3,
  from let h4 := case2_4_lem8 h h0 h1 h2 h3 in this.imp
  (or.imp 
    (λ h5, h4 _ $ (case2_4_lem5 h h0 h1 _).trans $
      sub_eq_neg_self.mpr $ sq_eq_zero_iff.mpr h5)
    (λ h5, eq_of_sub_eq_zero $ (char2.sub_eq_add h0 _ _).trans $ h4 _ $
      (case2_4_lem4 h h0 h1 x).trans $ sub_eq_neg_self.mpr $ sq_eq_zero_iff.mpr h5))
  (λ this, let h5 := (case2_4_lem6 h h0 h1 x).resolve_left
    (this.trans_ne $ add_left_ne_self.mpr h3) in
  ⟨h5, h4 _ $ (case2_4_lem3 h h0 _).trans $ begin
    have h6 := add_sq' (f x) (f (x + 1)),
    rw [h5, this, one_pow, bit1, add_right_comm, self_eq_add_left,
        mul_assoc, ← mul_one_add, mul_eq_zero] at h6,
    exact h6.elim (λ h6, absurd h6 h3) eq_neg_of_add_eq_zero_right
  end⟩),
---- Now prove that either `f(x) = 0`, `f(x + 1) = 0`, or `f(x)^2 + f(x + 1)^2 = 3`
suffices 2 * (f (x + 1) * f x) ^ 2 * (f x ^ 2 + f (x + 1) ^ 2 - 3) = 0,
  from (mul_eq_zero.mp this).imp (λ h4, mul_eq_zero.mp $ sq_eq_zero_iff.mp $
    (mul_eq_zero.mp h4).resolve_left h3) eq_of_sub_eq_zero,
begin
  have h4 : ∀ x, f (x ^ 4) = (f x ^ 2 - 1) ^ 2 - 1 :=
    λ x, by rw [bit0, ← two_mul, pow_mul, case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1],
  have h5 := case2_4_lem3 h h0,
  have h6 := char2.add_one_pow_four h0,
  have h7 := h4 (x * (x + 1) + 1),
  rw [h5, h6, mul_pow, h6, h5, h4, ← h6, h4, eq_comm, ← sub_eq_zero] at h7,
  rw ← h7, ring
end

lemma case2_4_lem10 (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (x : R) :
  (x = 0 ∨ x = 1) ∨ (f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0) :=
  (case2_4_lem9 h h0 h1 h2 h3 x).imp_left $ or.imp (h4 x) $ λ h5, eq_of_sub_eq_zero $ h4 _ $
    by rwa [char2.sub_eq_add h0, char2.add_one_sq h0, h5, ← bit0]



/-- The main lemma for the `𝔽₂[X]/⟨X^2⟩` subcase -/
lemma case2_4_𝔽₂ε_main_lemma {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
  ∀ x, (x = 0 ∨ x = c) ∨ (x = 1 ∨ x = c + 1) :=
suffices ∀ x, f (c * x + 1) = 0, from cases_of_nonperiod_quasi_period h h2 h1 this h4,
λ x, let h6 := (case2_4_lem5 h h0 h1 $ c * x).symm in
  by rwa [mul_pow, sq c, h5, zero_mul, h1, sub_eq_neg_self, sq_eq_zero_iff] at h6

lemma case2_4_𝔽₂ε_hom_bijective {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
  bijective (𝔽₂ε.cast'_hom h0 h5) :=
  ⟨𝔽₂ε.cast'_hom_injective _ _ h4,
  λ x, (case2_4_𝔽₂ε_main_lemma h h0 h1 h2 h3 h4 h5 x).elim
    (λ h5, h5.elim (λ h5, ⟨𝔽₂ε.O, h5.symm⟩) (λ h5, ⟨𝔽₂ε.X, h5.symm⟩))
    (λ h5, h5.elim (λ h5, ⟨𝔽₂ε.I, h5.symm⟩) (λ h5, ⟨𝔽₂ε.Y, h5.symm⟩))⟩

lemma case2_4_𝔽₂ε_quotient_sol {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
  f = 𝔽₂ε_map S ∘
    (ring_equiv.of_bijective _ $ case2_4_𝔽₂ε_hom_bijective h h0 h1 h2 h3 h4 h5).symm :=
(mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x, let h6 := good_map_one h in
match x with
| 𝔽₂ε.O := h1
| 𝔽₂ε.I := h6
| 𝔽₂ε.X := suffices f c = 1 ∨ f c = -1,
      from this.resolve_right $ mt (case2_4_lem8 h h0 h1 h2 h3 c) h4,
    by rwa [← sq_eq_one_iff, ← sub_eq_zero, ← case2_4_lem4 h h0 h1, sq, h5, zero_add]
| 𝔽₂ε.Y := let h7 := case2_4_lem5 h h0 h1 c in
    by rwa [sq, h5, h1, eq_comm, sub_eq_neg_self, sq_eq_zero_iff] at h7
end



/-- The main lemma for the `𝔽₄` subcase -/
lemma case2_4_𝔽₄_main_lemma (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
  {c : R} (h5 : f c + f (c + 1) = 1) (h6 : c * c + c = 1) :
  ∀ x, (x = 0 ∨ x = c) ∨ (x = 1 ∨ x = c + 1) :=
λ x, (or_or_or_comm _ _ _ _).mp $ let h7 := case2_4_lem10 h h0 h1 h2 h3 h4 in
(h7 x).imp_right $ λ h8, (h7 (x + c)).elim
  (or.imp (char2.add_eq_zero_iff_eq h0).mp (char2.add_eq_iff_eq_add' h0).mp)
  (let h9 := one_ne_zero_of_map_zero h h1 in suffices (x + c) * (x + c + 1) = 0,
    from λ h10, absurd h10.2 $ by rwa [this, zero_add],
  by rw [mul_add_one, ← sq, char2.add_sq h0,
    add_add_add_comm, sq, sq, h6, ← mul_add_one, h8.2])

lemma case2_4_𝔽₄_hom_bijective (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
  {c : R} (h5 : f c + f (c + 1) = 1) (h6 : c * c + c = 1) :
  bijective (𝔽₄.cast'_hom h0 h6) :=
  ⟨𝔽₄.cast'_hom_injective _ _ (one_ne_zero_of_map_zero h h1),
  λ x, (case2_4_𝔽₄_main_lemma h h0 h1 h2 h3 h4 h5 h6 x).elim
    (λ h5, h5.elim (λ h5, ⟨𝔽₄.O, h5.symm⟩) (λ h5, ⟨𝔽₄.X, h5.symm⟩))
    (λ h5, h5.elim (λ h5, ⟨𝔽₄.I, h5.symm⟩) (λ h5, ⟨𝔽₄.Y, h5.symm⟩))⟩

lemma case2_4_𝔽₄_quotient_sol (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
  {c : R} (h5 : f c + f (c + 1) = 1) (h6 : c * c + c = 1) :
  f = 𝔽₄_map S (f c) ∘
    (ring_equiv.of_bijective _ $ case2_4_𝔽₄_hom_bijective h h0 h1 h2 h3 h4 h5 h6).symm :=
(mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x,
match x with
| 𝔽₄.O := h1
| 𝔽₄.I := good_map_one h
| 𝔽₄.X := rfl
| 𝔽₄.Y := eq_sub_of_add_eq' h5
end



lemma case2_4_quotient_sol2 :
  (∃ φ : R ≃+* 𝔽₂ε, f = 𝔽₂ε_map S ∘ φ) ∨
  (∃ (φ : R ≃+* 𝔽₄) (s : S), s * (1 - s) = -1 ∧ f = 𝔽₄_map S s ∘ φ) ∨
  (∃ φ : R ≃+* 𝔽₂, f = 𝔽₂_map S ∘ φ) :=
  (em' $ ∀ x : R, x ^ 2 = 0 → x = 0).imp
---- `𝔽₂ε`
(λ h4, exists.elim (not_forall.mp h4) $ λ c h4, let h4 := not_imp.mp h4 in
  ⟨_, case2_4_𝔽₂ε_quotient_sol h h0 h1 h2 h3 h4.2 ((sq c).symm.trans h4.1)⟩) $
  λ h4, (em $ ∃ c, f c + f (c + 1) = 1 ∧ c * c + c = 1).imp
---- `𝔽₄`
(λ h5, exists.elim h5 $ λ c h5, ⟨_, (f c),
  by rw [← eq_sub_of_add_eq' h5.1, ← case2_4_lem3 h h0, mul_add_one, h5.2];
    exact (congr_arg f h0).trans h1, 
  case2_4_𝔽₄_quotient_sol h h0 h1 h2 h3 h4 h5.1 h5.2⟩)
---- `𝔽₂`
(λ h5, let h5 : ∀ x : R, x = 0 ∨ x = 1 :=
  λ x, (case2_4_lem10 h h0 h1 h2 h3 h4 x).resolve_right
    (λ h6, h5 ⟨x, h6.1, (mul_add_one x x).symm.trans $
      (char2.add_eq_zero_iff_eq h0).mp h6.2⟩) in
suffices bijective (𝔽₂.cast_hom h0), from ⟨(ring_equiv.of_bijective _ this).symm,
  (mul_equiv.eq_comp_symm _ _ _).mpr $ funext $ λ x,
    match x with | 𝔽₂.O := h1 | 𝔽₂.I := good_map_one h end⟩,
⟨𝔽₂.cast_hom_injective _ (one_ne_zero_of_map_zero h h1),
  λ x, (h5 x).elim (λ h5, ⟨𝔽₂.O, h5.symm⟩) (λ h5, ⟨𝔽₂.I, h5.symm⟩)⟩)

end Rchar2



lemma case2_4_lift_decomp1 (h0 : f (-1) = 0) (h1 : f 2 = -1) (h2 : (2 : S) = 0) :
  ∃ φ : R ⧸ period_ideal h →+* S, period_lift h = λ x, φ x - 1 :=
  let h3 := period_lift_is_good h,
    h4 := zero_of_periodic_period_lift h 2 $ case2_4_lem1 h3 h0 h1 in
  case2_4_quotient_sol1 h3 h4 ((congr_arg _ h4.symm).trans h1) h2

lemma case2_4_lift_decomp2 (h0 : f (-1) = 0) (h1 : f 2 = -1) (h2 : (2 : S) ≠ 0) :
  (∃ φ : R ⧸ period_ideal h ≃+* 𝔽₂ε, period_lift h = 𝔽₂ε_map S ∘ φ) ∨
  (∃ (φ : R ⧸ period_ideal h ≃+* 𝔽₄) (s : S),
    s * (1 - s) = -1 ∧ period_lift h = 𝔽₄_map S s ∘ φ) ∨
  (∃ φ : R ⧸ period_ideal h ≃+* 𝔽₂, period_lift h = 𝔽₂_map S ∘ φ) :=
  let h3 := period_lift_is_good h, h4 := zero_of_periodic_period_lift h,
    h5 := h4 2 $ case2_4_lem1 h3 h0 h1 in
  case2_4_quotient_sol2 h3 h5 ((congr_arg _ h5.symm).trans h1) h4 h2



/-- Solution for the current subcase -/
theorem case2_4_sol (h0 : f (-1) = 0) (h1 : f 2 = -1) :
  (∃ φ : R →+* S, f = λ x, φ x - 1) ∨
  (∃ φ : R →+* 𝔽₂ε, surjective φ ∧ f = 𝔽₂ε_map S ∘ φ) ∨
  (∃ (φ : R →+* 𝔽₄) (s : S), surjective φ ∧ s * (1 - s) = -1 ∧ f = 𝔽₄_map S s ∘ φ) ∨
  (∃ φ : R →+* 𝔽₂, surjective φ ∧ f = 𝔽₂_map S ∘ φ) :=
  (em $ (2 : S) = 0).imp
---- Map 1
(λ h2, exists.elim (case2_4_lift_decomp1 h h0 h1 h2) $ λ ψ h3,
  let π := ideal.quotient.mk (period_ideal h) in
    ⟨ψ.comp π, (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h3⟩) $
  λ h2, (case2_4_lift_decomp2 h h0 h1 h2).imp
---- Map 2
(λ h3, exists.elim h3 $ λ ψ h3, let π := ideal.quotient.mk (period_ideal h) in
  ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
    (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h3⟩) $ or.imp
---- Map 3
(λ h3, exists.elim h3 $ λ ψ h3, exists.elim h3 $ λ s h3,
  let π := ideal.quotient.mk (period_ideal h) in
  ⟨ψ.to_ring_hom.comp π, s, (equiv_like.surjective ψ).comp π.is_surjective,
    h3.1, (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h3.2⟩)
---- Map 4
(λ h3, exists.elim h3 $ λ ψ h3, let π := ideal.quotient.mk (period_ideal h) in
  ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
    (period_lift_comp_quotient_eq_f h).symm.trans $ congr_arg (∘ π) h3⟩)

end step10









/- ### Final solution -/

/-- Final solution -/
theorem final_solution {R S : Type*} [comm_ring R] [field S] {f : R → S} :
  good f ↔
    f = 0 ∨
    (∃ φ : R →+* S, f = λ x, φ x - 1) ∨
    (∃ φ : R →+* 𝔽₃, surjective φ ∧ f = 𝔽₃_map1 S ∘ φ) ∨
    ((∃ φ : R →+* 𝔽₂ε, surjective φ ∧ f = 𝔽₂ε_map S ∘ φ) ∨
     (∃ (φ : R →+* 𝔽₄) (s : S), surjective φ ∧ s * (1 - s) = -1 ∧ f = 𝔽₄_map S s ∘ φ) ∨  
     (∃ φ : R →+* 𝔽₂, surjective φ ∧ f = 𝔽₂_map S ∘ φ)) ∨
    (∃ φ : R →+* ℤ₄, surjective φ ∧ f = ℤ₄_map S ∘ φ) ∨
    (∃ φ : R →+* S, f = λ x, φ x ^ 2 - 1) ∨
    (∃ φ : R →+* 𝔽₃, surjective φ ∧ f = 𝔽₃_map2 S ∘ φ) :=
⟨λ h, (ne_or_eq (f 0) (-1)).imp (eq_zero_of_map_zero_ne_neg_one h) $
  λ h0, (ne_or_eq (f (-1)) 0).elim
  (λ h1, (eq_or_ne (f (-1)) (-2)).imp (case1_1_sol h h1) $
    λ h2, or.inl $ case1_2_sol h h1 h2 $ (case1_map_neg_one_cases h h1).resolve_left h2)
  (λ h1, (eq_or_ne (f 2) (-1)).elim
    (λ h2, (case2_4_sol h h1 h2).imp_right $ λ h3, (or.inl h3).inr)
    (λ h2, or.inr $ or.inr $ or.inr $
      (eq_or_ne (f 2) 1).elim (λ h3, or.inl $ case2_2_sol h h1 h3 h2) $
      λ h3, or.inr $ (eq_or_ne (f 2) 3).imp (λ h4, case2_3_sol h h1 h4 h3 h0) $ 
        λ h4, suffices f 2 = 0, from case2_1_sol h h1 h0 this h4,
          (((case2_map_two_cases h h1 h0).resolve_left h2).resolve_left h3).resolve_left h4)),
λ h, h.elim (λ h, h.symm ▸ zero_is_good) $
  λ h, h.elim (λ h, exists.elim h $ λ φ h, h.symm ▸ good_map_comp_hom sub_one_is_good φ) $
  λ h, h.elim (λ h, exists.elim h $ λ φ h, h.2.symm ▸ good_map_comp_hom 𝔽₃_map1_is_good φ) $
  λ h, h.elim
    (λ h, h.elim (λ h, exists.elim h $ λ φ h, h.2.symm ▸ good_map_comp_hom 𝔽₂ε_map_is_good φ) $
      λ h, h.elim (λ h, exists.elim h $ λ φ h, exists.elim h $ λ s h, h.2.2.symm ▸
        good_map_comp_hom (𝔽₄_map_is_good h.2.1) φ) $
      λ h, exists.elim h $ λ φ h, h.2.symm ▸ good_map_comp_hom 𝔽₂_map_is_good φ)
    (λ h, h.elim (λ h, exists.elim h $ λ φ h, h.2.symm ▸ good_map_comp_hom ℤ₄_map_is_good φ) $
      λ h, h.elim (λ h, exists.elim h $ λ φ h, h.symm ▸ good_map_comp_hom sq_sub_one_is_good φ) $
        λ h, exists.elim h $ λ φ h, h.2.symm ▸ good_map_comp_hom 𝔽₃_map2_is_good φ)⟩

end IMO2012A5
end IMOSL
