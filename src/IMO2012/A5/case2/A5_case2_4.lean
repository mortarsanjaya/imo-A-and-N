import
  IMO2012.A5.case2.A5_case2_lemmas
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.F2
  IMO2012.A5.explicit_rings.F4
  algebra.dual_number

/-! # IMO 2012 A5, Case 2.4: `f(2) = -1` -/

namespace IMOSL
namespace IMO2012A5

section answers

variables (R : Type*) [ring R]

/-- The first respective solution for the subcase. -/
def 𝔽₂_map : 𝔽₂ → R
| 𝔽₂.O := -1
| 𝔽₂.I := 0

theorem case2_3_answer1 : good (𝔽₂_map R)
| 𝔽₂.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₂.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₂_map R) $
    add_comm _ _).trans (zero_mul _).symm

/-- The second respective solution for the subcase. -/
def 𝔽₄_map (φ : R) : 𝔽₄ → R
| 𝔽₄.O := -1
| 𝔽₄.I := 0
| 𝔽₄.X := φ
| 𝔽₄.Y := 1 - φ

theorem case2_3_answer2 {φ : R} (h : φ * (1 - φ) = -1) : good (𝔽₄_map R φ)
| 𝔽₄.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₄.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₄_map R φ) $
    add_comm _ _).trans (zero_mul _).symm
| 𝔽₄.X 𝔽₄.O := (zero_sub φ).trans (mul_neg_one φ).symm
| 𝔽₄.X 𝔽₄.I := (sub_self _).trans (mul_zero φ).symm
| 𝔽₄.X 𝔽₄.X := sub_eq_of_eq_add $ eq_add_of_sub_eq' $ (mul_one_sub φ φ).symm.trans h
| 𝔽₄.X 𝔽₄.Y := (sub_zero (-1)).trans h.symm
| 𝔽₄.Y 𝔽₄.O := (zero_sub _).trans (mul_neg_one _).symm
| 𝔽₄.Y 𝔽₄.I := (sub_self φ).trans (mul_zero _).symm
| 𝔽₄.Y 𝔽₄.X := (sub_zero (-1)).trans $ h.symm.trans $
    (mul_one_sub φ φ).trans (one_sub_mul φ φ).symm
| 𝔽₄.Y 𝔽₄.Y := sub_eq_of_eq_add $ eq_add_of_sub_eq' $
  (one_sub_mul _ _).symm.trans $ (congr_arg (* (1 - φ)) (sub_sub_cancel 1 φ)).trans h

/-- The third respective solution for the subcase. -/
def 𝔽₂ε_map : dual_number 𝔽₂ → R
| (𝔽₂.O, 𝔽₂.O) := -1
| (𝔽₂.O, 𝔽₂.I) := 1
| (𝔽₂.I, _) := 0

theorem case2_3_answer3 : good (𝔽₂ε_map R)
| (𝔽₂.O, 𝔽₂.O) (x, y) := (zero_sub _).trans (neg_one_mul _).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.O, 𝔽₂.O) := (zero_sub 1).trans (one_mul (-1)).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.O, 𝔽₂.I) := (zero_sub (-1)).trans $ (neg_neg 1).trans (one_mul 1).symm
| (𝔽₂.O, 𝔽₂.I) (𝔽₂.I, y) := (sub_self 0).trans (one_mul 0).symm
| (𝔽₂.I, b) (𝔽₂.O, y) := (sub_self 0).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.O) (𝔽₂.I, 𝔽₂.O) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.O) (𝔽₂.I, 𝔽₂.I) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.I) (𝔽₂.I, 𝔽₂.O) := (sub_self _).trans (zero_mul _).symm
| (𝔽₂.I, 𝔽₂.I) (𝔽₂.I, 𝔽₂.I) := (sub_self _).trans (zero_mul _).symm

end answers



section noncomm_ring

variables {R S : Type*} [ring R] [ring S] [is_domain S] {f : R → S} (h : good f) 
include h

private lemma case2_4_lem1 (h0 : f (-1) = 0) (h1 : f 2 = -1) (x : R) :
  f x + f (x - 1) = -1 ∨ f (x + 1) = f (x - 1) :=
  by have h2 := case2_special_identity h h0 x; rwa [case2_map_add_two_eq h h0, h1,
    mul_neg_one, neg_sub, sub_add_comm, mul_neg_one, neg_add_cancel_comm_assoc,
    mul_add, (map_comm_of_comm h $ (commute.refl x).sub_left $ commute.one_left x).eq,
    ← sub_sub, sub_right_comm, ← mul_sub, ← neg_sub (f (x + 1)), mul_neg, ← neg_mul,
    ← sub_mul, sub_neg_eq_add, ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero] at h2

private lemma case2_4_lem2 (h0 : f (-1) = 0) 
  (h1 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h2 : f 2 = -1) : (2 : R) = 0 :=
  h1 2 $ λ x,
begin
  have h3 := case2_4_lem1 h h0 h2 (x + 1),
  rw [add_sub_cancel, add_assoc, add_comm x (1 + 1)] at h3,
  revert h3; refine (or_iff_right_of_imp $ λ h3, _).mp,
  have h4 := (case2_4_lem1 h h0 h2 (-(x + 1))).symm,
  rw [← neg_add', case2_map_is_even h h0, case2_map_is_even h h0, neg_add', sub_add_cancel,
      case2_map_is_even h h0, add_assoc, add_comm x (1 + 1), eq_comm] at h4,
  revert h4; refine (or_iff_left_of_imp $ λ h4, _).mp,
  rwa [← h3, add_right_inj] at h4
end

variables (h0 : (2 : R) = 0)
include h0

private lemma case2_4_lem3 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  by rw [← h, ← add_assoc, ← two_mul, h0, zero_mul, zero_add, good_map_one h, sub_zero]

variables (h1 : f 0 = -1)
include h1

private lemma case2_4_lem4 (x : R) : f (x * x + 1) = f x * f x - 1 :=
  by rw [← h, ← two_mul, h0, zero_mul, h1, sub_neg_eq_add, add_sub_cancel]

private lemma case2_4_lem5 (x : R) :
  (f x * f x - 1) * (f x - 1) + f x * f (x + 1) = f (x + 1) * f ((x + 1) * x) :=
begin
  /- Somehow the proof takes 0.2s -/
  rw [← case2_4_lem4 h h0 h1, ← case2_4_lem3 h h0, ← h, mul_sub_one, ← add_sub_right_comm],
  refine congr_arg2 has_sub.sub (add_eq_of_eq_sub _) (congr_arg f _),
  rw [← mul_assoc, add_one_mul, mul_add_one, add_assoc, ← add_assoc x,
      ← two_mul, h0, zero_mul, zero_add, add_right_comm, h],
  rw [add_right_comm, add_left_inj, add_one_mul,
      add_left_comm, ← two_mul, h0, zero_mul, add_zero]
end

end noncomm_ring



section comm_ring

section general

variables {R S : Type*} [ring R] [comm_ring S] [is_domain S]

private lemma case2_4_lem6_1' (a b : S) :
  a * ((a * a - 1) * (a - 1) + a * b) - b * ((b * b - 1) * (b - 1) + b * a) =
    (a - b) * ((a * a + b * b - 1) * (a + b - 1)) :=
  by ring

private lemma case2_4_lem6_1 {a b : S}
  (h : a * ((a * a - 1) * (a - 1) + a * b) = b * ((b * b - 1) * (b - 1) + b * a)) :
    a = b ∨ (a * a + b * b = 1) ∨ (a + b = 1) :=
  by rwa [← sub_eq_zero, case2_4_lem6_1', mul_eq_zero,
    mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h

private lemma case2_4_lem6_2' (a : S) : a * a * ((a * a - 1) * (a * a - 1)) -
  (((a * a - 1) * (a - 1) + a * a) * ((a * a - 1) * (a - 1) + a * a) - a * a) =
    (1 - (a + a)) * (a * a - 1) :=
  by ring

private lemma case2_4_lem6_2 {a : S} (h : a * a * ((a * a - 1) * (a * a - 1)) =
  (((a * a - 1) * (a - 1) + a * a) * ((a * a - 1) * (a - 1) + a * a) - a * a)) :
  a + a = 1 ∨ a * a = 1 :=
  by rwa [← sub_eq_zero, case2_4_lem6_2', mul_eq_zero,
    sub_eq_zero, sub_eq_zero, eq_comm] at h

variables {f : R → S} (h : good f) (h0 : (2 : R) = 0) (h1 : f 0 = -1)
include h h0 h1

private lemma case2_4_lem6_3 (x : R) :
  f (x + 1) = f x ∨ f (x + 1) * f (x + 1) + f x * f x = 1 ∨ f (x + 1) + f x = 1 :=
  case2_4_lem6_1 $
begin
  have h2 := case2_4_lem5 h h0 h1 (x + 1),
  rw [add_assoc, ← bit0, h0, add_zero] at h2,
  rw [h2, case2_4_lem5 h h0 h1, mul_left_comm, mul_add_one, add_one_mul]
end

private lemma case2_4_lem6_4 {x : R} (h2 : f (x + 1) = f x) :
  f x + f x = 1 ∨ f x * f x = 1 :=
  case2_4_lem6_2 $
begin
  have h3 : (x + 1) * (x + 1) = x * x + 1 := by rw [add_one_mul, mul_add_one,
    add_assoc, ← add_assoc x, ← two_mul, h0, zero_mul, zero_add],
  have h4 := case2_4_lem4 h h0 h1 ((x + 1) * x),
  rw [((commute.refl x).add_right $ commute.one_right x).mul_mul_mul_comm, h3,
      add_one_mul, ← mul_add_one, case2_4_lem3 h h0, case2_4_lem4 h h0 h1,
      ← add_zero (x * x), ← h0, bit0, ← add_assoc, ← h3, case2_4_lem4 h h0 h1, h2] at h4,
  replace h4 := congr_arg (has_mul.mul $ f (x + 1) * f (x + 1)) h4,
  rwa [mul_sub_one (f _ * _), mul_mul_mul_comm _ _ (f _), ← case2_4_lem5 h h0 h1, h2] at h4
end

private lemma case2_4_lem6 (x : R) :
  f (x + 1) * f (x + 1) + f x * f x = 1 ∨ f (x + 1) + f x = 1 :=
  (case2_4_lem6_3 h h0 h1 x).symm.elim id $ λ h2, or.inr $
  (case2_4_lem6_4 h h0 h1 h2).elim (congr_arg (+ f x) h2).trans $ λ h3, 
begin
  replace h2 := congr_arg2 has_mul.mul h2 h2,
  rw [h3, ← sub_eq_zero, ← case2_4_lem4 h h0 h1, add_one_mul, mul_add_one, add_right_comm,
      add_assoc (x * x), add_assoc, ← two_mul, h0, zero_mul, add_zero] at h2,
  rw [← sub_eq_zero, ← case2_4_lem4 h h0 h1, ← h2] at h3,
  replace h3 := case2_4_lem6_4 h h0 h1 h3,
  rw [h2, add_zero, mul_zero, or_self] at h3,
  exact absurd h3 zero_ne_one
end

end general



section char_S_eq_two

variables {R S : Type*} [ring R] [comm_ring S] [is_domain S]

private lemma case2_4_1_lem1 (a b c : S) :
  (a * (b + 1) + c) * (b * (a + 1) + c) - 1 -
    (a * b + c + 1) * ((b + 1) * (a + 1) + (c + 1)) =
  c - (a + b + 1) - 2 * (a * b + 2 * c + 1) :=
  by ring

variables (h : (2 : R) = 0) (h0 : (2 : S) = 0) {f : R → S} (h1 : good f) (h2 : f 0 = -1)
include h h0 h1 h2

private lemma case2_4_1_lem3 (x : R) : f (x + 1) = f x + 1 :=
begin
  rw [← add_left_inj (f x), add_right_comm, ← two_mul, h0, zero_mul, zero_add],
  refine (case2_4_lem6 h1 h h2 x).elim (λ h3, _) id,
  have h4 := add_mul_self_eq (f (x + 1)) (f x),
  rwa [h0, zero_mul, zero_mul, add_zero, h3, mul_self_eq_one_iff,
      neg_eq_of_add_eq_zero_right h0, or_self] at h4
end

private lemma case2_4_1_lem4 (x y : R) : f (x * y) = f x * f y + f (x + y) + 1 :=
  by rw [← eq_add_of_sub_eq (h1 x y), case2_4_1_lem3 h h0 h1 h2,
    add_assoc, ← bit0, h0, add_zero]

private lemma case2_4_1_lem5 (x y : R) : f (x * (y + 1)) = f x * (f y + 1) + f (x + y) :=
  by rw [case2_4_1_lem4 h h0 h1 h2, case2_4_1_lem3 h h0 h1 h2, add_assoc, add_right_inj,
    ← add_assoc, case2_4_1_lem3 h h0 h1 h2, add_assoc, ← bit0, h0, add_zero]

private lemma case2_4_1_lem6 (x y : R) : f (x + y) = f x + f y + 1 :=
begin
  have h3 := h1 (x * y) ((y + 1) * (x + 1)),
  conv_lhs at h3 { congr,
    rw [← mul_assoc, mul_assoc x, mul_add_one y, ← add_one_mul,
        ← mul_assoc, mul_assoc, eq_add_of_sub_eq (h1 _ _)],
    congr, skip, congr,
    rw [mul_add_one, mul_add_one, add_add_add_comm], skip,
    rw [mul_add_one, add_one_mul, add_assoc, ← add_assoc (x * y),
        ← add_assoc x, ← add_assoc, case2_4_1_lem3 h h0 h1 h2] },
  rw [← sub_sub, add_sub_cancel] at h3,
  iterate 3 { rw case2_4_1_lem5 h h0 h1 h2 at h3 },
  rw [case2_4_1_lem3 h h0 h1 h2, add_right_comm, add_comm y x, case2_4_1_lem4 h h0 h1 h2,
      case2_4_1_lem3 h h0 h1 h2, ← sub_eq_zero, case2_4_1_lem1, h0, zero_mul, sub_zero] at h3,
  exact eq_of_sub_eq_zero h3
end

private lemma case2_4_1_lem7 (x y : R) : f (x * y) + 1 = (f x + 1) * (f y + 1) :=
  by rw [case2_4_1_lem4 h h0 h1 h2, add_assoc, ← bit0, h0, add_zero,
    case2_4_1_lem6 h h0 h1 h2, add_assoc, ← add_assoc, ← mul_add_one, ← add_one_mul]

theorem case2_4_1_sol : ∃ φ : R →+* S, f = λ x, φ x - 1 :=
  ⟨⟨λ x, f x + 1,
      add_left_eq_self.mpr (good_map_one h1),
      case2_4_1_lem7 h h0 h1 h2,
      add_eq_zero_iff_eq_neg.mpr h2,
      λ x y, by rw [case2_4_1_lem6 h h0 h1 h2, add_add_add_comm, add_assoc]⟩,
    funext (λ x, by rw [ring_hom.coe_mk, add_sub_cancel])⟩

end char_S_eq_two



section char_S_ne_two

/- Nothing yet -/

end char_S_ne_two

end comm_ring

end IMO2012A5
end IMOSL
