import algebra.char_p.two

/-! # IMO 2009 A7 -/

namespace IMOSL
namespace IMO2009A7

def good {R : Type*} [ring R] (f : R → R) :=
  ∀ x y : R, f (x * f (x + y)) = f (f x * y) + x ^ 2



section basic_results

variables {R : Type*} [ring R]

private lemma good_id : good (id : R → R) :=
  λ x y, (mul_add x x y).trans $ (add_comm _ _).trans $ congr_arg (has_add.add _) (sq x).symm

variables [is_domain R] {f : R → R} (h : good f)
include h

private lemma good_map_zero : f 0 = 0 :=
begin
  have h0 := h 0 (f (f 0)),
  rw [zero_mul, sq, zero_mul, add_zero] at h0,
  replace h := h (f 0) 0,
  rw [add_zero, ← h0, mul_zero, self_eq_add_right] at h,
  exact pow_eq_zero h
end

private lemma good_self_mul_map (x : R) : f (x * f x) = x ^ 2 :=
  by have h0 := h x 0; rwa [add_zero, mul_zero, good_map_zero h, zero_add] at h0

private lemma good_inj : function.injective f :=
begin
  suffices : ∀ x : R, f x = 0 ↔ x = 0,
  { intros x y h0,
    have h1 := good_self_mul_map h y,
    rw [← h0, ← add_sub_cancel'_right y x, h, add_left_eq_self,
        this, mul_eq_zero, this, sub_eq_zero] at h1,
    exact h1.elim (λ h2, ((this x).mp $ h0.trans $ (this y).mpr h2).trans h2.symm) id },
  
  refine λ x, ⟨λ h0, _, λ h0, (congr_arg f h0).trans (good_map_zero h)⟩,
  have h1 := good_self_mul_map h x,
  rw [h0, mul_zero, good_map_zero h, eq_comm] at h1,
  exact pow_eq_zero h1
end

private lemma good_odd (x : R) : f (-x) = -f x :=
begin
  have h0 := good_self_mul_map h (-x),
  rw [neg_sq, ← good_self_mul_map h, neg_mul] at h0,
  replace h0 := good_inj h h0,
  rw [← add_eq_zero_iff_neg_eq, ← mul_add, mul_eq_zero, add_eq_zero_iff_eq_neg] at h0,
  revert h0; refine (or_iff_right_of_imp _).mp,
  rintros rfl; rwa [neg_zero, good_map_zero h, neg_zero]
end

private lemma good_map_one_sq : f 1 ^ 2 = 1 :=
begin
  have h0 := good_self_mul_map h 1,
  rw [one_mul, one_pow] at h0,
  replace h := good_self_mul_map h (f 1),
  rwa [h0, mul_one, h0, eq_comm] at h
end

private lemma good_neg : good (-f) :=
  λ x y, by calc
    _ = f (-(x * -f (x + y))) : (good_odd h _).symm
    ... = f (x * f (x + y)) : by rw [mul_neg, neg_neg]
    ... = f (f x * y) + x ^ 2 : h x y
    ... = -f (-f x * y) + x ^ 2 : by rw [← good_odd h, neg_mul, neg_neg]

end basic_results







/-- Final solution, case 1: `char(R) ≠ 2` -/
theorem final_solution_char_ne_two {R : Type*} [ring R] [is_domain R] (Rchar : ring_char R ≠ 2) :
  ∀ f : R → R, good f ↔ (f = λ x, x) ∨ (f = λ x, -x) :=
begin
  ---- Reduce just to proving that if `f` is good and `f(1) = 1`, then `f` is the identity
  suffices : ∀ f : R → R, good f → f 1 = 1 → f = λ x, x,
  { refine λ f, ⟨λ h, _, λ h, _⟩,
    cases sq_eq_one_iff.mp (good_map_one_sq h) with h0 h0,
    left; exact this f h h0,
    right; rw [← pi.neg_def, eq_neg_iff_add_eq_zero, ← neg_eq_iff_add_eq_zero],
    exact this (-f) (good_neg h) (neg_eq_iff_eq_neg.mpr h0),
    rcases h with rfl | rfl,
    exacts [good_id, good_neg good_id] },
  
  ---- Show that `f(x + 2) = f(x) + 2` for all `x : R`
  intros f h h0,
  replace h0 : ∀ x : R, f (x + 2) = f x + 2 :=
  begin
    intros x,
    have h1 := h (-1) (x + 2),
    rwa [neg_sq, neg_mul, good_odd h, bit0, add_left_comm, neg_add_cancel_comm_assoc,
         add_comm, h, one_pow, good_odd h, h0, one_mul, neg_one_mul, good_odd h,
         neg_eq_iff_add_eq_zero, add_left_comm, neg_add_eq_zero, add_assoc] at h1
  end,

  ---- Finishing
  funext x,
  have h1 := h 2 x,
  rw [sq, two_mul (2 : R), ← add_assoc, ← h0, ← h0] at h1,
  replace h1 := good_inj h h1,
  nth_rewrite 2 ← zero_add (2 : R) at h1,
  rwa [h0, good_map_zero h, zero_add, add_comm, h0, mul_add,
       add_assoc, ← two_mul, add_left_inj, mul_eq_mul_left_iff] at h1,
  revert h1; exact (or_iff_left (ring.two_ne_zero Rchar)).mp
end



/-- Final solution, case 2: `char(R) = 2` -/
theorem final_solution_char_eq_two {R : Type*} [ring R] [is_domain R] [char_p R 2]
  (f : R → R) : good f ↔ f = λ x, x :=
begin
  refine ⟨λ h, _, λ h, cast (congr_arg good h).symm good_id⟩,
  have h0 := good_map_one_sq h,
  rw [sq_eq_one_iff, char_two.neg_eq, or_self] at h0,
  suffices : ∀ c d : R, f c = d + 1 → f d = c + 1 → (c = d ∨ c = d + 1),
  { replace h0 : ∀ x : R, f (f (x + 1)) = f x + 1 :=
      λ x, by have h1 := h 1 x; rwa [one_mul, h0, one_mul, one_pow, add_comm] at h1,
    funext x; replace this := this (f (x + 1)) (f x) (h0 x),
    rw [← h0, add_assoc, char_two.add_self_eq_zero, add_zero] at this,
    replace this := this rfl; cases this with h1 h1,
    replace h1 := good_inj h h1,
    exfalso; revert h1,
    rw add_right_eq_self; exact one_ne_zero,
    replace h0 := h0 (x + 1),
    rw [h1, add_assoc, add_assoc, char_two.add_self_eq_zero, add_zero, add_zero] at h0,
    exact good_inj h h0 },

  ---- Prove the claim
  suffices : ∀ c d : R, f c = d + 1 → c * d = d * c,
  { replace h0 : ∀ c d : R, f c = d + 1 → f((d + 1) * (c + 1)) = c ^ 2 + d + 1 :=
      λ c d h1, by rw [add_assoc, ← h1, ← sub_eq_iff_eq_add', char_two.sub_eq_add,
        ← h, ← add_assoc, char_two.add_self_eq_zero, zero_add, h0, mul_one],
    intros c d h1 h2,
    replace this := this c d h1,
    replace h1 := h0 c d h1,
    rw [add_one_mul, mul_add_one, ← this, ← add_one_mul, ← mul_add_one, h0 d c h2] at h1,
    clear h0 h2 h f,
    replace this : (c - d) * (c + d) = c ^ 2 - d ^ 2 :=
      by rw [sub_mul, mul_add, mul_add, this, sq, sq, add_comm, add_sub_add_left_eq_sub],
    rw [add_left_inj, add_comm, ← sub_eq_sub_iff_add_eq_add, ← this, eq_comm,
        mul_right_eq_self₀, sub_eq_zero, ← char_two.sub_eq_add, sub_eq_iff_eq_add'] at h1,
    exact h1.symm },

  intros c d h1,
  replace h0 := h c c,
  rw [char_two.add_self_eq_zero, good_map_zero h, mul_zero, good_map_zero h,
      eq_comm, add_eq_zero_iff_eq_neg, char_two.neg_eq, ← good_self_mul_map h] at h0,
  replace h0 := good_inj h h0,
  rwa [h1, add_one_mul, mul_add_one, add_left_inj, eq_comm] at h0
end

/-- Final solution -/
theorem final_solution {R : Type*} [ring R] [is_domain R] :
  ∀ f : R → R, good f ↔ f = (λ x, x) ∨ f = (λ x, -x) :=
begin
  cases ne_or_eq (ring_char R) 2 with h h,
  exact final_solution_char_ne_two h,
  haveI : char_p R 2 := ring_char.of_eq h,
  rw char_two.neg_eq',
  exact λ f, (final_solution_char_eq_two f).trans (or_self _).symm
end

end IMO2009A7
end IMOSL
