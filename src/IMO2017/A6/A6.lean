import algebra.char_p.two

/-! # IMO 2017 A6 (P2) -/

namespace IMOSL
namespace IMO2017A6

open function

def good {R : Type*} [ring R] (f : R → R) :=
  ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y)



section basic_results

section ring

variables {R : Type*} [ring R]

private lemma good_zero : good (0 : R → R) :=
  λ _ _, add_zero 0
  
private lemma good_one_sub_self : good (has_sub.sub (1 : R)) :=
  λ x y, by rw [sub_add, sub_right_inj, sub_eq_iff_eq_add',
    ← add_sub_right_comm, ← sub_sub_sub_eq, ← one_sub_mul, ← mul_one_sub]

variables {f : R → R} (h : good f)
include h

private lemma good_neg : good (-f) :=
  λ x y, (neg_add _ _).symm.trans $ congr_arg has_neg.neg $
    (congr_arg (λ z, f z + f (x + y)) $ neg_mul_neg _ _).trans (h x y)

private lemma good_special_equality {x y : R} (h0 : x * y = 1) :
  f (f (x + 1) * f (y + 1)) = 0 :=
  add_left_eq_self.mp $ (h _ _).trans $
    by rw [add_one_mul, mul_add_one, h0, add_comm 1 x]

private lemma good_map_map_zero_sq : f (f 0 ^ 2) = 0 :=
  by replace h := h 0 0; rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h

private lemma good_map_eq_one_sub_self_of_inj (h0 : f 0 = 1) (h1 : injective f) :
  f = λ x, 1 - x :=
begin
  -- Reduce to `f(f(x)) + f(x) = 1` for all `x : R`
  suffices h2 : ∀ x : R, f (f x) + f x = 1,
  { funext x; rw [← h2 x, eq_sub_iff_add_eq, add_comm, add_left_inj],
    apply h1; rw [← add_left_inj (f (f x)), h2, add_comm, h2] },
  
  -- Prove `f(f(x)) + f(x) = 1` for all `x : R`
  intros x; replace h := h x 0,
  rwa [mul_zero, h0, mul_one, add_zero] at h
end

end ring


section division_ring

variables {R : Type*} [division_ring R] {f : R → R} (h : good f)
include h

private lemma good_map_eq_zero {c : R} (h0 : f ≠ 0) (h1 : f c = 0) : c = 1 :=
begin
  contrapose h0; rw not_not,

  -- First prove `f(0) = 0`.
  rw ← sub_eq_zero at h0,
  replace h0 := good_special_equality h (mul_inv_cancel h0),
  rw [sub_add_cancel, h1, zero_mul] at h0,

  -- Now use `f(0) = 0` to prove `f = 0`.
  funext x; replace h := h 0 x,
  rwa [zero_add, zero_mul, h0, zero_mul, h0, zero_add] at h
end

private lemma good_map_zero_sq (h0 : f ≠ 0) : f 0 ^ 2 = 1 :=
  good_map_eq_zero h h0 (good_map_map_zero_sq h)

private lemma good_map_one : f 1 = 0 :=
  or.elim (eq_or_ne f 0) (λ h0, congr_fun h0 1) $
    λ h0, (congr_arg f $ good_map_zero_sq h h0).symm.trans (good_map_map_zero_sq h)

private lemma good_shift (h0 : f 0 = 1) (x : R) : f (x + 1) + 1 = f x :=
  by have h1 := h x 1; rwa [good_map_one h, mul_zero, h1, mul_one, add_comm, h0] at h1

private lemma good_map_eq_zero_iff (h0 : f 0 = 1) (c : R) : f c = 0 ↔ c = 1 :=
  ⟨good_map_eq_zero h (λ h1, absurd ((congr_fun h1 0).symm.trans h0) zero_ne_one),
    λ h1, (congr_arg f h1).trans (good_map_one h)⟩

end division_ring

end basic_results







/-- Final solution, `char(R) ≠ 2` -/
theorem final_solution_char_ne_two {R : Type*} [division_ring R] (Rchar : ring_char R ≠ 2) :
  ∀ f : R → R, good f ↔ (f = 0 ∨ f = has_sub.sub 1 ∨ (f = λ x, x - 1)) :=
begin
  ---- Change `f = λ x, x - 1` to `-f = λ x, 1 - x`, which is way more convenient to handle
  intros f; conv_rhs { congr, skip, congr, skip, rw ← neg_inj,
    congr, skip, rw pi.neg_def, funext, rw neg_sub },

  ---- `←` direction: easy
  symmetry; refine ⟨λ h, _, λ h, _⟩,
  rcases h with rfl | rfl | h,
  exact good_zero,
  exact good_one_sub_self,
  rw ← neg_neg f; apply good_neg,
  rw h; exact good_one_sub_self,

  ---- `→` direction: reduce to showing that `f(0) = 1` implies `f = λ x, 1 - x`
  rw or_iff_not_imp_left; revert h f,
  suffices : ∀ {f : R → R}, good f → f 0 = 1 → f = has_sub.sub 1,
  { intros f h h0,
    replace h0 := good_map_zero_sq h h0,
    rw sq_eq_one_iff at h0; cases h0 with h0 h0,
    left; exact this h h0,
    right; refine this (good_neg h) _,
    rw [pi.neg_apply, h0, neg_neg] },
  
  ---- Some setup
  intros f h h0,
  have h1 := good_shift h h0,
  have h2 : ∀ t : R, f (f (-1) * f t) + f t + 1 = f (-t) :=
    λ t, by rw [← neg_one_mul t, ← h (-1), add_assoc, ← h1 (-1 + t), neg_add_cancel_comm],

  ---- Reduce to `∀ c, f c = f (-c) → c = 0`
  suffices h3 : ∀ {c}, f c = f (-c) → c = 0,
  { refine good_map_eq_one_sub_self_of_inj h h0 (λ a b h4, _),
    rw ← sub_eq_zero; apply h3,
    replace h2 : ∀ {x y}, f x = f y → f (-x) = f (-y) := λ x y h5, by rw [← h2, h5, h2],
    replace h1 : f (a * b) = f (b * a) := by rw [← h, ← h b a, h4, add_comm a],
    replace h0 := h a (-b),
    rwa [h4, ← h2 h4, mul_neg, h2 h1, ← mul_neg, ← h b, add_right_inj,
         ← sub_eq_add_neg, ← sub_eq_add_neg, ← neg_sub a] at h0 },

  ---- Prove `∀ c, f(c) = f(-c) → c = 0`
  intros c h3; rw ← h2 at h3,
  replace h2 := good_map_eq_zero_iff h h0,
  rwa [add_right_comm, self_eq_add_left, ← sub_add_cancel (_ * f c) 1, h1, h2, sub_eq_iff_eq_add,
       ← h1, neg_add_self, h0, mul_right_eq_self₀, ← bit0, or_iff_left (ring.two_ne_zero Rchar),
       ← h1, add_left_eq_self, h2, add_left_eq_self] at h3
end



/-- Final solution, `F` is a field, `char(F) = 2` -/
theorem final_solution_field_char_two {F : Type*} [field F] [char_p F 2] :
  ∀ f : F → F, good f ↔ f = 0 ∨ f = has_add.add 1 :=
begin
  ---- `←` direction: easy
  rw ← char_two.sub_eq_add',
  intros f; symmetry; refine ⟨λ h, _, λ h, _⟩,
  { rcases h with rfl | rfl,
    exacts [good_zero, good_one_sub_self] },
  
  ---- `→` direction: Reduce to showing that if `f(0) ≠ 0`, then `f` is injective
  rw or_iff_not_imp_left; intros h0,
  replace h0 := good_map_zero_sq h h0,
  rw [sq_eq_one_iff, char_two.neg_eq, or_self] at h0,
  refine good_map_eq_one_sub_self_of_inj h h0 (λ a b h1, _),

  ---- First, remove the case `a = 0` and `b = 0`
  have X := good_shift h h0,
  have X0 := good_map_eq_zero_iff h h0,
  rw [← X, ← X b, add_left_inj] at h1,
  rcases eq_or_ne a 0 with rfl | ha,
  rwa [zero_add, good_map_one h, eq_comm, X0, add_left_eq_self, eq_comm] at h1,
  rcases eq_or_ne b 0 with rfl | hb,
  rwa [zero_add, good_map_one h, X0, add_left_eq_self] at h1,

  ---- Reduce to `f(x + y) = f(xy + 1)`, where `x = a + b + 1` and `y = a⁻¹ + b⁻¹ + 1`
  let x := a + b + 1; let y := a⁻¹ + b⁻¹ + 1,
  suffices : f (x + y) + 1 = f (x * y),
  { replace h := h x y,
    rw [← this, add_comm, add_right_inj, ← X, add_left_eq_self,
        X0, add_left_eq_self, mul_eq_zero, X0, X0] at h,
    cases h with h h; rw [add_left_eq_self, add_eq_zero_iff_eq_neg, char_two.neg_eq] at h,
    exacts [h, inv_inj.mp h] },
  rw [← X (x * y), add_left_inj],
  dsimp only [x, y]; clear x y,
  
  ---- A general lemma, applied on the pair `(a, b⁻¹)` and `(b, a⁻¹)`
  replace X : ∀ c d : F, c ≠ 0 → d ≠ 0 → f (c + 1) = f (d + 1) →
    f (c + d⁻¹ + 1) = f (c * d⁻¹ + c + d⁻¹) :=
  begin
    intros c d hc hd hcd,
    have hcd0 := h (c + 1) (d⁻¹ + 1),
    rwa [hcd, good_special_equality h (mul_inv_cancel hd), zero_add, ← add_left_inj (1 : F),
         add_add_add_comm, ← add_assoc, add_one_mul, mul_add_one, ← add_assoc, X, X] at hcd0
  end,
  replace X0 := X a b ha hb h1,
  replace X := X b a hb ha h1.symm,
  clear h0 h1,
  
  ---- Reduce to two identities, then prove them
  rw [add_add_add_comm, add_comm a⁻¹, add_add_add_comm a, add_add_add_comm,
      ← add_right_inj (f (f (a + b⁻¹ + 1) * f (b + a⁻¹ + 1))), h, eq_comm, X0, X],
  clear X0 X; convert h (a * b⁻¹ + a + b⁻¹) (b * a⁻¹ + b + a⁻¹) using 2,
  { apply congr_arg; clear h f,
    rw [add_one_mul, add_assoc, add_assoc (b⁻¹ + a⁻¹), char_two.add_self_eq_zero,
        add_zero, add_add_add_comm, add_left_inj, add_add_add_comm, mul_add_one,
        add_left_inj, add_mul, mul_add, mul_add, mul_inv_cancel ha, mul_inv_cancel hb,
        add_comm (1 : F), add_add_add_comm, char_two.add_self_eq_zero, add_zero] },
  { rw [← mul_left_inj' ha, mul_assoc, mul_assoc, ← mul_right_inj' hb, ← mul_assoc,
        ← mul_assoc b, mul_comm, mul_comm b, mul_comm (b * _ + _ + _) a],
    clear h f; revert a b ha hb,
    suffices : ∀ {a b : F}, a ≠ 0 → b ≠ 0 → (b + a⁻¹ + 1) * a = b * (a * b⁻¹ + a + b⁻¹),
      intros a b ha hb; rw [this ha hb, this hb ha],
    intros a b ha hb,
    rw [add_right_comm, add_mul, inv_mul_cancel ha, mul_add, ← mul_add_one,
        mul_left_comm, mul_add_one, mul_inv_cancel hb, add_comm b, mul_comm] }
end



/-- Final solution, `F` is a field -/
theorem final_solution_field {F : Type*} [field F] :
  ∀ f : F → F, good f ↔ (f = 0 ∨ f = has_sub.sub 1 ∨ (f = λ x, x - 1)) :=
begin
  cases ne_or_eq (ring_char F) 2 with h h,
  exact final_solution_char_ne_two h,
  haveI : char_p F 2 := ring_char.of_eq h,
  intros f; rw [final_solution_field_char_two f, char_two.sub_eq_add'],
  conv_rhs { congr, skip, congr, skip, congr, skip, funext, rw add_comm },
  rw or_self
end

end IMO2017A6
end IMOSL
