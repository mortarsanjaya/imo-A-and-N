import algebra.order.ring.defs algebra.group_power.ring tactic.ring

/-! # IMO 2016 A7, Generalized Version -/

namespace IMOSL
namespace IMO2016A7

open function

/- ### Extra lemmas -/

lemma hom_sub_one_is_good_ring_id {R : Type*} [comm_ring R] (x y : R) :
  (x + y - 1) ^ 2 = 2 * (x - 1) * (y - 1) + (x ^ 2 + y ^ 2 - 1) :=
  by ring

lemma eq_zero_or_hom_of_map_add_map_sq {R S : Type*}
  [comm_semiring R] [comm_ring S] [is_domain S] [char_zero S]
  {f : R → S} (h : ∀ x y : R, f (x + y) = f x + f y) (h0 : ∀ x : R, f (x ^ 2) = f x ^ 2) :
  f = 0 ∨ ∃ φ : R →+* S, f = φ :=
suffices (f 1 = 0 ∨ f 1 = 1) ∧ (∀ x y : R, f (x * y) = f x * f y),
from this.1.imp
  (λ h1, funext $ λ x, by rw [pi.zero_apply, ← mul_one x, this.2, h1, mul_zero])
  (λ h1, ⟨⟨f, h1, this.2, add_right_cancel ((h 0 0).symm.trans $
      (congr_arg f $ zero_add 0).trans (zero_add _).symm), h⟩, rfl⟩),
---- `f(1) ∈ {0, 1}`
⟨(mul_right_eq_self₀.mp $ (sq $ f 1).symm.trans $
  (h0 1).symm.trans $ congr_arg f $ one_pow 2).symm,
λ x y, begin
  have h1 := h0 (x + y),
  rw [h, add_sq', h, h, h0, h0, add_sq', add_right_inj, mul_assoc,
      two_mul, h, ← two_mul, mul_assoc, mul_eq_mul_left_iff] at h1,
  refine h1.resolve_right _,
  rw [← nat.cast_two, nat.cast_eq_zero],
  exact nat.succ_ne_zero 1
end⟩





/- ### Start of the Problem -/

section semiring_ring

variables {R S : Type*} [semiring R] [linear_ordered_ring S]

def good (f : R → S) := ∀ x y : R,
  f (x + y) ^ 2 = 2 * f x * f y + max (f (x ^ 2) + f (y ^ 2)) (f (x ^ 2 + y ^ 2))

/- #### Answer -/

lemma zero_is_good : good (λ _ : R, (0 : S)) :=
  λ x y, (zero_pow $ nat.succ_pos 1).trans $ (add_zero 0).symm.trans $
    congr_arg2 has_add.add (mul_zero _).symm $ (max_self 0).symm.trans $
      congr_arg2 max (add_zero 0).symm rfl

lemma neg_one_is_good : good (λ _ : R, (-1 : S)) :=
  λ x y, neg_one_sq.trans $ (add_neg_cancel_right 1 1).symm.trans $ congr_arg2 has_add.add
    ((mul_neg_one _).trans $ (congr_arg has_neg.neg $ mul_neg_one 2).trans $ neg_neg _).symm
    (max_eq_right $ add_le_of_nonpos_left $ neg_nonpos.mpr $ zero_le_one' S).symm

end semiring_ring


section semiring_comm_ring

variables {R S : Type*} [semiring R] [linear_ordered_comm_ring S]

lemma hom_is_good (φ : R →+* S) : good φ :=
  λ x y, (congr_arg (λ x : S, x ^ 2) (φ.map_add x y)).trans $
    (add_sq' _ _).trans $ (add_comm _ _).trans $ congr_arg (has_add.add _) $
      (congr_arg2 has_add.add (φ.map_pow _ 2).symm (φ.map_pow _ 2).symm).trans $
        (max_eq_left $ le_of_eq $ φ.map_add (x ^ 2) (y ^ 2)).symm

lemma hom_sub_one_is_good (φ : R →+* S) : good (λ x : R, φ x - 1) :=
  λ x y, (congr_arg (λ x : S, (x - 1) ^ 2) (φ.map_add x y)).trans $
    (hom_sub_one_is_good_ring_id (φ x) (φ y)).trans $ congr_arg (has_add.add _) $
    (congr_arg (λ x : S, x - 1) $ (congr_arg2 has_add.add (φ.map_pow x 2).symm
      (φ.map_pow y 2).symm).trans (φ.map_add _ _).symm).trans $
    (max_eq_right $ (sub_add_sub_comm _ _ _ _).trans_le $
      sub_le_sub (le_of_eq (φ.map_add (x ^ 2) (y ^ 2)).symm) one_le_two).symm





/- #### Solution -/

variables {f : R → S} (h : good f)
include h

lemma good_map_zero : f 0 = 0 ∨ f 0 = -1 :=
begin
  replace h := h 0 0,
  rw [mul_assoc, ← sq, zero_pow (nat.succ_pos 1), add_zero,
      two_mul, add_assoc, self_eq_add_right, sq] at h,
  refine (le_or_lt 0 (f 0)).imp (λ h0, _) (λ h0, _),
  { rw [max_eq_left (le_add_of_nonneg_left h0), ← two_mul, ← add_mul, mul_eq_zero] at h,
    exact h.resolve_left (ne_of_gt $ add_pos_of_nonneg_of_pos h0 two_pos) },
  { rw [max_eq_right (add_le_of_nonpos_left $ le_of_lt h0), ← add_one_mul, mul_eq_zero] at h,
    exact eq_neg_of_add_eq_zero_left (h.resolve_right $ ne_of_lt h0) }
end

lemma good_map_sq (x : R) : f (x ^ 2) = f x ^ 2 - 2 * f 0 * f x :=
begin
  have h0 : f 0 ≤ 0 := (good_map_zero h).elim le_of_eq
    (λ h0, h0.trans_le $ neg_nonpos.mpr $ zero_le_one' S),
  have h := (h 0 x).symm,
  rwa [zero_add, zero_pow (nat.succ_pos 1), zero_add,
       max_eq_right (add_le_of_nonpos_left h0), ← eq_sub_iff_add_eq'] at h
end

lemma good_map_main_ineq (x y : R) :
  2 * f x * f y + (f (x ^ 2) + f (y ^ 2)) ≤ f (x + y) ^ 2 :=
  (add_le_add_left (le_max_left _ _) _).trans_eq (h x y).symm

end semiring_comm_ring


section ring_comm_ring

variables {R S : Type*} [ring R] [linear_ordered_comm_ring S] {f : R → S} (h : good f)
include h

lemma good_map_neg (x : R) : f (-x) + f x = 2 * f 0 ∨ f (-x) = f x :=
  by have h0 := (good_map_sq h $ -x).symm; rwa [neg_sq, good_map_sq h,
    sub_eq_sub_iff_sub_eq_sub, sq_sub_sq, ← mul_sub, mul_eq_mul_right_iff, sub_eq_zero] at h0



/- ##### Case 1: `f(0) = 0` -/

section map_zero_eq_zero

variables (h0 : f 0 = 0)
include h0

lemma good_case1_map_sq (x : R) : f (x ^ 2) = f x ^ 2 :=
  (good_map_sq h x).trans $ sub_eq_self.mpr $
    mul_eq_zero_of_left (mul_eq_zero_of_right 2 h0) (f x)

lemma good_case1_map_neg (x : R) : f (-x) = -f x :=
(good_map_neg h x).elim
(λ h1, eq_neg_of_add_eq_zero_left $ h1.trans $ mul_eq_zero_of_right 2 h0)
(λ h1, begin
  have h2 := good_map_main_ineq h x (-x),
  rw [add_neg_self, h0, zero_pow (nat.succ_pos 1), h1, mul_assoc, ← sq, neg_sq,
      good_case1_map_sq h h0, ← two_mul, ← add_mul, ← two_mul, ← sq, ← mul_pow] at h2,
  replace h2 := pow_eq_zero (le_antisymm h2 $ sq_nonneg _),
  rw [mul_eq_zero, or_iff_right (two_ne_zero' S)] at h2,
  rw [h1, h2, neg_zero]
end)

lemma good_case1_map_add_sq_sub_map_sub_sq (x y : R) :
  f (x + y) ^ 2 - f (x - y) ^ 2 = 2 * (2 * f x * f y) :=
  by have h1 := congr_arg2 has_sub.sub (h x y) (h x (-y));
    rwa [neg_sq, add_sub_add_right_eq_sub, ← sub_eq_add_neg,
      good_case1_map_neg h h0, mul_neg, sub_neg_eq_add, ← two_mul] at h1

lemma good_case1_map_two_mul (x : R) : f (2 * x) = 2 * f x :=
begin
  have h1 := good_case1_map_add_sq_sub_map_sub_sq h h0 x x,
  rw [sub_self, h0, zero_pow (nat.succ_pos 1), sub_zero, ← two_mul, mul_assoc,
      ← sq, ← mul_assoc, ← sq, ← mul_pow, sq_eq_sq_iff_eq_or_eq_neg] at h1,
  refine h1.elim id (λ h2, _),
  replace h1 := (sq_nonneg _).trans_eq (eq_add_of_sub_eq $
    good_case1_map_add_sq_sub_map_sub_sq h h0 (2 * x) x),
  rw [h2, mul_neg, neg_mul, mul_assoc, mul_assoc, ← sq, two_mul x,
      add_sub_cancel, mul_neg, ← mul_assoc, ← sq, ← mul_assoc,
      ← pow_succ', le_neg_add_iff_le, ← sub_nonpos, ← sub_one_mul] at h1,
  have h3 : (1 : S) < 2 ^ (2 + 1) := one_lt_pow one_lt_two (nat.succ_ne_zero 2),
  replace h1 := le_antisymm h1 (mul_nonneg (le_of_lt $ sub_pos.mpr h3) (sq_nonneg _)),
  rw [mul_eq_zero, sub_eq_zero, or_iff_right (ne_of_gt h3)] at h1,
  rw [h2, pow_eq_zero h1, mul_zero, neg_zero]
end

lemma good_case1_map_sq_sub_map_sq (x y : R) : f x ^ 2 - f y ^ 2 = f (x + y) * f (x - y) :=
  by have h1 := good_case1_map_add_sq_sub_map_sub_sq h h0 (x + y) (x - y);
    rwa [add_add_sub_cancel, ← two_mul, good_case1_map_two_mul h h0,
      mul_pow, add_sub_sub_cancel, ← two_mul, good_case1_map_two_mul h h0,
      mul_pow, ← mul_sub, mul_assoc, ← mul_assoc, ← sq, mul_eq_mul_left_iff,
      or_iff_left (pow_ne_zero 2 $ two_ne_zero' S)] at h1

lemma good_case1_abs_map_add (x y : R) : |f (x + y)| = |f x + f y| :=
begin
  have h1 := good_map_main_ineq h x y,
  rw [good_case1_map_sq h h0, good_case1_map_sq h h0,
      add_comm, ← add_sq', le_iff_eq_or_lt] at h1,
  refine ((sq_eq_sq_iff_abs_eq_abs _ _).mp $ h1.resolve_right $ λ h2, _).symm,
  replace h1 := good_case1_map_add_sq_sub_map_sub_sq h h0 x y,
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at h1,
  replace h1 := (sub_lt_sub_right h2 _).trans_eq h1,
  rw [two_mul, add_sq', add_sub_add_right_eq_sub, ← sub_sq'] at h1,
  rw sq_lt_sq at h1 h2,

  have h3 := congr_arg has_abs.abs (good_case1_map_sq_sub_map_sq h h0 x y),
  rw [abs_mul, sq_sub_sq, abs_mul] at h3,
  revert h3; exact ne_of_lt (mul_lt_mul'' h2 h1 (abs_nonneg _) (abs_nonneg _))
end

lemma good_case1_map_add (x y : R) : f (x + y) = f x + f y :=
  (abs_eq_abs.mp $ good_case1_abs_map_add h h0 x y).elim id $ λ h1,
begin
  have h2 := good_case1_abs_map_add h h0 (x + y) (-y),
  rw [add_neg_cancel_right, good_case1_map_neg h h0, abs_eq_abs] at h2,
  cases h2 with h2 h2,
  rwa [eq_add_neg_iff_add_eq, eq_comm] at h2,
  rw [h1, ← neg_add, neg_neg, add_assoc, self_eq_add_right, ← two_mul,
      mul_eq_zero, or_iff_right (ne_of_gt $ zero_lt_two' S)] at h2,
  have h3 := good_case1_abs_map_add h h0 (x + y) (-x),
  rw [add_neg_cancel_comm, h2, abs_zero, eq_comm, abs_eq_zero,
      good_case1_map_neg h h0, add_neg_eq_zero] at h3,
  rw [h3, h2, add_zero]
end

end map_zero_eq_zero



/- ##### Case 2: `f(0) = -1` -/

section map_zero_eq_neg_one

variables (h0 : f 0 = -1)
include h0

lemma good_case2_map_sq (x : R) : f (x ^ 2) = f x ^ 2 + 2 * f x :=
  (good_map_sq h x).trans $ by rw [h0, mul_neg_one, neg_mul, sub_neg_eq_add]

lemma good_case2_map_sq_add_one (x : R) : f (x ^ 2) + 1 = (f x + 1) ^ 2 :=
  by rw [add_sq, mul_one, ← good_case2_map_sq h h0, one_pow]

lemma good_case2_map_neg_prelim (x : R) : f (-x) = f x ∨ f (-x) + f x = -2 :=
begin
  have h1 := (good_case2_map_sq h h0 (-x)).symm,
  rw [neg_sq, good_case2_map_sq h h0, add_comm, ← sub_eq_sub_iff_add_eq_add,
      sq_sub_sq, ← neg_sub, ← mul_sub, ← neg_mul, mul_eq_mul_right_iff] at h1,
  exact h1.symm.imp (λ h1, (sub_eq_zero.mp h1).symm) (λ h1, (add_comm _ _).trans h1.symm)
end

lemma good_case2_map_add_sub_map_neg_add (x y : R) :
  f (x + y) - f(-(x + y)) = f (-x) * f (-y) - f x * f y :=
begin
  have h1 := congr_arg2 has_sub.sub (h (-x) (-y)) (h x y),
  rw [neg_sq, neg_sq, add_sub_add_right_eq_sub,
      ← neg_add, mul_assoc, mul_assoc, ← mul_sub] at h1,
  have h2 : (2 : S) ≠ 0 := two_ne_zero' S,
  cases good_case2_map_neg_prelim h h0 (x + y) with h3 h3,
  { rw [h3, sub_self, zero_eq_mul, or_iff_right h2] at h1,
    rw [h1, h3, sub_self] },
  { rwa [sq_sub_sq, h3, neg_mul, ← mul_neg, neg_sub,
         mul_eq_mul_left_iff, or_iff_left h2] at h1 }
end

lemma good_case2_map_neg_eq_map_self_imp_ne_one {x : R} (h1 : f (-x) = f x) : f x ≠ 1 :=
begin
  intros h3,
  have h2 := good_map_main_ineq h x (-x),
  rw [neg_sq, h1, add_neg_self, h0, neg_sq, ← two_mul, good_case2_map_sq h h0, h3, mul_one,
      mul_one, ← mul_one_add, one_pow, ← add_assoc, ← bit0, ← two_mul, ← sq, ← pow_succ] at h2,
  exact not_lt_of_le h2 (one_lt_pow one_lt_two $ nat.succ_ne_zero 2)
end

lemma good_case2_map_neg_non_even_case {c : R} (h1 : f (-c) ≠ f c) (x : R) :
  f (-x) + f x = -2 :=
(good_case2_map_neg_prelim h h0 x).symm.elim id $
λ h2, begin
  have X := good_case2_map_add_sub_map_neg_add h h0,
  have h3 := X (c + x) (-x),
  rw [add_neg_cancel_right, neg_neg, h2, ← sub_mul, ← neg_sub (f (c + x)), X, h2,
      ← sub_mul, ← neg_mul, neg_sub, mul_assoc, eq_comm, mul_right_eq_self₀,
      or_iff_left (sub_ne_zero_of_ne h1.symm), ← sq, sq_eq_one_iff,
      or_iff_right (good_case2_map_neg_eq_map_self_imp_ne_one h h0 h2)] at h3,
  rw [h2, h3, ← neg_add, bit0] 
end

lemma good_case2_even_map_add_self (h1 : ∀ x, f (-x) = f x) (x : R) : f (x + x) = -1 :=
  by have h2 := h x (-x);
  rw [add_neg_self, neg_sq, h1, ← h, h0, neg_one_sq, eq_comm, sq_eq_one_iff] at h2;
  exact h2.resolve_left (good_case2_map_neg_eq_map_self_imp_ne_one h h0 $ h1 _)

lemma good_case2_even_map_values' (h1 : ∀ x, f (-x) = f x) (x : R) :
  f x = -1 ∨ (0 < f x ∧ 4 * (f x ^ 2 + f x) = 1) :=
begin
  have X := good_case2_even_map_add_self h h0 h1,
  have X0 : 0 < (2 : S) := zero_lt_two' S,
  have h3 := h x x,
  rw [X, X, neg_one_sq, ← two_mul, mul_assoc, ← sq, good_case2_map_sq h h0] at h3,
  refine (le_total (2 * (f x ^ 2 + 2 * f x)) (-1)).imp (λ h4, _) (λ h4, _),
  ---- Case 1: `2 f(x)^2 + 4 f(x) ≤ -1`
  { rw [max_eq_right h4, eq_add_neg_iff_add_eq, ← bit0, eq_comm,
        mul_right_eq_self₀, or_iff_left (ne_of_gt X0), sq_eq_one_iff] at h3,
    exact h3.resolve_left (good_case2_map_neg_eq_map_self_imp_ne_one h h0 $ h1 x) },
  ---- Case 2: `2 f(x)^2 + 4 f(x) ≥ -1`
  { rw max_eq_left h4 at h3,
    rw [← add_le_add_iff_left (2 * f x ^ 2), ← h3, add_neg_le_iff_le_add,
        ← two_mul, mul_le_mul_left X0, sq_le_one_iff_abs_le_one] at h4,
    rw [← mul_add, ← add_assoc, ← two_mul, ← mul_add, ← mul_assoc, two_mul] at h3,
    refine ⟨lt_of_not_le (λ h5, ne_of_gt ((zero_lt_one' S).trans_le' _) h3), h3.symm⟩,
    rw [abs_eq_neg_self.mpr h5, neg_le_iff_add_nonneg'] at h4,
    rw [sq, ← add_one_mul],
    exact mul_nonpos_of_nonneg_of_nonpos (zero_le_bit0.mpr $ le_of_lt X0)
      (mul_nonpos_of_nonneg_of_nonpos h4 h5) }
end

lemma good_case2_even_map_values (h1 : ∀ x, f (-x) = f x) (x : R) : f x = -1 :=
(good_case2_even_map_values' h h0 h1 x).resolve_right $ λ h2,
have f x < f (x ^ 2) :=
  by rw [good_case2_map_sq h h0, two_mul, ← add_assoc];
    exact lt_add_of_pos_left _ (add_pos (pow_pos h2.1 2) h2.1),
(good_case2_even_map_values' h h0 h1 (x ^ 2)).elim
  (λ h3, not_le_of_lt (h2.1.trans this) $ h3.trans_le $ neg_nonpos.mpr $ zero_le_one' S)
  (λ h3, absurd (h2.2.trans h3.2.symm) $ ne_of_lt $ mul_lt_mul_of_pos_left
    (add_lt_add (sq_lt_sq' ((neg_lt_zero.mpr h3.1).trans h2.1) this) this)
    (zero_lt_four' S))

lemma good_case2_map_neg_eq (x : R) : f (-x) = -(f x + 2) :=
(em $ ∀ x, f (-x) = f x).elim
  (λ h1, let X := good_case2_even_map_values h h0 h1 in
    (X _).trans $ by rw [X, bit0, neg_add_cancel_comm_assoc])
  (λ h1, exists.elim (not_forall.mp h1) $ λ c h1, eq_neg_of_add_eq_zero_left $
    (add_assoc _ _ _).symm.trans $ add_eq_zero_iff_eq_neg.mpr $
    good_case2_map_neg_non_even_case h h0 h1 x)

lemma good_case2_map_add_one_add (x y : R) : f (x + y) + 1 = (f x + 1) + (f y + 1) :=
  let X := good_case2_map_neg_eq h h0 in
  by have h1 := good_case2_map_add_sub_map_neg_add h h0 x y;
    rwa [X, sub_neg_eq_add, ← add_assoc, ← two_mul, ← mul_add_one,
      X, X, neg_mul_neg, add_mul, mul_add (f x), add_assoc,
      add_sub_cancel', mul_comm (f x), ← mul_add, mul_eq_mul_left_iff,
      or_iff_left (two_ne_zero' S), bit0, ← add_assoc, add_add_add_comm] at h1

end map_zero_eq_neg_one

end ring_comm_ring





/- #### Final solution -/

/-- Final solution -/
theorem final_solution {R S : Type*} [comm_ring R] [linear_ordered_comm_ring S] {f : R → S} :
  good f ↔ (f = 0 ∨ ∃ φ : R →+* S, f = φ) ∨ (f = (λ _, -1) ∨ ∃ φ : R →+* S, f = λ x, φ x - 1) :=
⟨λ h, (good_map_zero h).imp
  (λ h0, eq_zero_or_hom_of_map_add_map_sq (good_case1_map_add h h0) (good_case1_map_sq h h0))
  (λ h0, let h1 : (λ x, f x + 1) = 0 ∨ ∃ φ : R →+* S, (λ x, f x + 1) = φ :=
    eq_zero_or_hom_of_map_add_map_sq (good_case2_map_add_one_add h h0)
      (good_case2_map_sq_add_one h h0) in h1.imp
    (λ h1, funext $ λ x, eq_neg_of_add_eq_zero_left $ congr_fun h1 x)
    (λ h1, exists.elim h1 $ λ φ h1, ⟨φ, funext $ λ x, eq_sub_of_add_eq $ congr_fun h1 x⟩)),
λ h, h.elim
  (λ h, h.elim
    (λ h, cast (congr_arg good h.symm) zero_is_good)
    (λ h, exists.elim h $ λ φ h, cast (congr_arg good h.symm) (hom_is_good φ)))
  (λ h, h.elim
    (λ h, cast (congr_arg good h.symm) neg_one_is_good)
    (λ h, exists.elim h $ λ φ h, cast (congr_arg good h.symm) (hom_sub_one_is_good φ)))⟩

end IMO2016A7
end IMOSL
