import algebra.ring.regular

/-! # IMO 2015 A4 (P5) -/

namespace IMOSL
namespace IMO2015A4

variables {R : Type*} [ring R]

def good (f : R → R) :=
  ∀ x y : R, f (x + f (x + y)) + f (x * y) = x + f (x + y) + f x * y



lemma good_id : good (id : R → R) :=
  λ x y, rfl

lemma good_two_sub : good (has_sub.sub (2 : R)) :=
  λ x y, add_sub_assoc x 2 (x + y) ▸ (add_sub_add_left_eq_sub 2 y x).symm ▸
    (sub_sub_cancel 2 y).symm ▸ (sub_mul 2 x y).symm ▸ add_sub_assoc y 2 (x * y) ▸ 
    add_sub_assoc (2 - y) (2 * y) (x * y) ▸ (two_mul y).symm ▸
    congr_arg2 _ ((add_comm y 2).trans (sub_add_add_cancel 2 y y).symm) rfl
 


variables [is_domain R] {f : R → R}

lemma good_char_ne_two_imp (h : good f) (h0 : (2 : R) ≠ 0) :
  f = has_sub.sub 2 ∨ f = id :=
---- (1)
have h1 : ∀ t : R, f (t + f (t + 1)) = t + f (t + 1),
  from λ t, add_left_injective (f (t * 1)) $ (h t 1).trans $ congr_arg2 _ rfl $
    (mul_one _).trans $ congr_arg f (mul_one t).symm,
(ne_or_eq (f 0) 0).imp
---- Case `f(0) ≠ 0`
(λ h2, suffices ∀ t, t + f (t + 1) = 1 ∨ f 0 = 0, from funext $ λ t, sub_add_cancel t 1 ▸
  (add_sub_add_right_eq_sub 1 (t - 1) 1).symm ▸ eq_sub_of_add_eq' ((this _).resolve_right h2),
λ t, mul_right_eq_self₀.mp $ add_right_injective _ $ (h _ _).symm.trans $
  congr_arg2 _ (let y := t + f (t + 1) in (zero_add y).symm ▸
    (zero_add (f y)).symm ▸ congr_arg f (h1 t)) (congr_arg f $ zero_mul _))
---- Case `f(0) = 0`
(λ h2, have h3 : f (-1) = -1 := add_zero (-1 : R) ▸ h2 ▸ neg_add_self (1 : R) ▸ h1 _,
-- `f(1) = 1`
have h4 : f 1 = 1 :=
  let h4 := h 1 (-1) in by
  rwa [add_neg_self, h2, add_zero, one_mul, h3, mul_neg_one,
    add_neg_eq_iff_eq_add, add_right_comm, eq_add_neg_iff_add_eq,
    ← two_mul, ← two_mul, mul_eq_mul_left_iff, or_iff_left h0] at h4,
-- Reduce to `f` being odd
suffices ∀ x : R, f (-x) = -f x,
  from funext $ λ x,
  begin
    have h5 := h 1 x,
    rw [one_mul, h4, one_mul] at h5,
    have h6 := h (-1) (-x),
    rw [← neg_add, this, ← neg_add, this, this, h4, neg_mul_neg, one_mul] at h6,
    have h7 := congr_arg2 has_add.add h5 h6,
    rwa [add_add_add_comm, add_neg_self, zero_add, add_add_add_comm, add_neg_self, zero_add,
         ← two_mul, ← two_mul, mul_eq_mul_left_iff, or_iff_left h0] at h7
  end,
-- Prove that `f` is odd
λ x, begin
  rw [← mul_neg_one, ← add_right_inj (f (x + f (x + -1))), h,
      mul_neg_one, add_left_inj, eq_comm, ← sub_eq_add_neg],
  obtain ⟨y, rfl⟩ : ∃ y : R, y + (1 + 1) = x := ⟨x - (1 + 1), sub_add_cancel x _⟩,
  rw [add_sub_assoc, add_sub_cancel, ← bit0, add_right_comm],
  replace h1 := h1 y,
  have h5 := h (y + 1) 0,
  rw [add_zero, mul_zero, mul_zero, add_zero, h2, add_zero, add_right_comm] at h5,
  let t := y + f (y + 1),
  have h6 := h 1 t,
  rwa [h4, one_mul, h1, add_left_inj, add_comm 1 t, h5, add_left_comm] at h6
end)

lemma good_char_eq_two_imp (h : good f) (h0 : (2 : R) = 0) : f = id :=
---- Work with `g = x ↦ f(x) - x` instead of `f`
let g := λ x, f x - x in
suffices ∀ x, g x = 0, from funext $ λ x, eq_of_sub_eq_zero (this x),
have h : ∀ x y, g (y + g (x + y)) = g x * y - g (x * y) :=
  λ x y, suffices x + f (x + y) = y + (f (x + y) - (x + y)),
    from this ▸ (sub_eq_sub_iff_add_eq_add.mpr $ (h x y).trans (add_comm _ _)).trans
      ((sub_mul (f x) x y).symm ▸ (sub_sub_sub_cancel_right (f x * y) (f (x * y)) (x * y)).symm),
  (add_comm _ _).trans $ add_sub_left_comm (f (x + y)) y (x + y) ▸ congr_arg2 _ rfl $
    eq_sub_of_add_eq $ (add_assoc x x y).symm.trans $ add_left_eq_self.mpr $
    (two_mul x).symm.trans (mul_eq_zero_of_left h0 x),
---- Reduce into (3) and (4)
suffices (∀ t : R, g (t + 1) * (t + 1) = g t * t) ∧ ∀ t : R, g (g t * t) = g t,
  from λ x, let h1 := this.1 x,
    h2 := (this.2 (x + 1)).symm.trans $ (congr_arg g h1).trans (this.2 x) in
  by rwa [h2, mul_add_one, add_right_eq_self] at h1,
---- Set-up `g(0) = 0` and `g(1) = 0`
have h1 : g 0 = 0 ∧ g 1 = 0 :=
begin
  have h1 := h 1 1,
  rw [mul_one, mul_one, sub_self, ← bit0, h0, add_comm] at h1,
  have h2 := h 0 (g 0 + 1),
  rw [zero_mul, zero_add, h1, add_zero, h1, mul_add_one, add_sub_cancel, zero_eq_mul_self] at h2,
  rw [h2, zero_add] at h1,
  exact ⟨h2, h1⟩
end,
---- (3)
⟨λ t, begin
  have h : ∀ t : R, g (t + 1) + g (t * (t + 1)) = g t * (t + 1) :=
    λ t, add_eq_of_eq_sub $ h t (t + 1) ▸ add_assoc t t 1 ▸ two_mul t ▸
      (mul_eq_zero_of_left h0 t).symm ▸ (zero_add (1 : R)).symm ▸
      h1.2.symm ▸ congr_arg g (add_zero _).symm,
  have h2 := h (t + 1),
  rw [add_assoc, ← bit0, h0, add_zero] at h2,
  rw [mul_add_one, ← h2, add_one_mul, ← mul_add_one, add_assoc, add_comm (g (t * _)),
    h, mul_add_one, add_left_comm, ← two_mul, mul_eq_zero_of_left h0, add_zero]
end,
---- (4)
λ t, begin
  have h2 := h t 0,
  rw [add_zero, zero_add, mul_zero, mul_zero, h1.1, sub_self] at h2,
  have h3 := h 0 t,
  rw [zero_add, zero_mul, h1.1, zero_mul, sub_self, add_comm] at h3,
  have h4 := h (g t) t,
  rw [h3, add_zero, h2, zero_mul, zero_sub, ← neg_one_mul,
      neg_eq_of_add_eq_zero_left h0, one_mul] at h4,
  exact h4.symm
end⟩





/-- Final solution -/
theorem final_solution : good f ↔ f = (λ x, 2 - x) ∨ f = id :=
⟨λ h, (ne_or_eq (2 : R) 0).elim (good_char_ne_two_imp h)
  (λ h0, or.inr $ good_char_eq_two_imp h h0),
λ h, h.elim (λ h, h.symm ▸ good_two_sub) (λ h, h.symm ▸ good_id)⟩

end IMO2015A4
end IMOSL
