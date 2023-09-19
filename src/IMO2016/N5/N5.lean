import data.int.basic data.nat.sqrt tactic.ring

/-! # IMO 2016 N5 -/

namespace IMOSL
namespace IMO2016N5

def nice (k a x y : ℤ) := (k + 1) * y ^ 2 - k * x ^ 2 = a





/- ### Main observation -/

lemma main_identity (k x y : ℤ) :
  (k + 1) * (2 * k * x + (2 * k + 1) * y) ^ 2
    - k * ((2 * k + 1) * x + 2 * (k + 1) * y) ^ 2
    = (k + 1) * y ^ 2 - k * x ^ 2 :=
  by ring

lemma main_nice_lemma {k a x y : ℤ} (h : nice k a x y) :
  nice k a ((2 * k + 1) * x + 2 * (k + 1) * y) (2 * k * x + (2 * k + 1) * y) :=
  (main_identity k x y).trans h



/- ### Part 1 -/

lemma ascent_lemma {P : ℤ → Prop} (h : ∃ x, P x) (h0 : ∀ x, P x → ∃ x', x < x' ∧ P x') :
  ∀ N, ∃ x, N ≤ x ∧ P x :=
  exists.elim h $ λ x0 h N, int.induction_on' N x0 ⟨x0, le_refl x0, h⟩
    (λ k _ h1, exists.elim h1 $ λ y h1, exists.elim (h0 y h1.2) $ λ z h2,
      ⟨z, int.add_one_le_of_lt $ h1.1.trans_lt h2.1, h2.2⟩)
    (λ k _ h1, exists.elim h1 $ λ y h1,
      ⟨y, (int.sub_one_lt_of_le $ le_refl k).le.trans h1.1, h1.2⟩)

lemma nice_abs_abs {k a x y : ℤ} (h : nice k a x y) : nice k a (|x|) (|y|) :=
  (congr_arg2 _ (congr_arg2 _ rfl $ sq_abs y) (congr_arg2 _ rfl $ sq_abs x)).trans h

lemma y_ne_zero_of_a_pos_k_nonneg {k a : ℤ} (h : 0 ≤ k) (h0 : 0 < a)
  {x y : ℤ} (h1 : nice k a x y) : y ≠ 0 :=
  (sq_pos_iff y).mp $ pos_of_mul_pos_right ((add_pos_of_pos_of_nonneg h0 $
    mul_nonneg h $ sq_nonneg x).trans_eq (eq_add_of_sub_eq h1).symm) (int.le_add_one h)
  
lemma ascent_step {k a : ℤ} (h : 0 ≤ k) (h0 : 0 < a) {x : ℤ} (h1 : ∃ y, nice k a x y) :
  ∃ x', x < x' ∧ ∃ y, nice k a x' y :=
exists.elim h1 $ λ y h1,
  ⟨(2 * k + 1) * |x| + 2 * (k + 1) * |y|,
  lt_add_of_le_of_pos
    ((le_abs_self x).trans $ le_mul_of_one_le_left (abs_nonneg x) $
      le_add_of_nonneg_left $ mul_nonneg zero_le_two h)
    (mul_pos (mul_pos two_pos $ int.lt_add_one_of_le h)
      (abs_pos.mpr $ y_ne_zero_of_a_pos_k_nonneg h h0 h1)),
  2 * k * |x| + (2 * k + 1) * |y|,
  main_nice_lemma $ nice_abs_abs h1⟩



/-- Final solution, part 1 -/
theorem final_solution_part1 {k a : ℤ} (h : 0 ≤ k) (h0 : 0 < a) (h1 : ∃ x y, nice k a x y) :
  ∀ N, ∃ x, N ≤ x ∧ ∃ y, nice k a x y :=
  ascent_lemma h1 $ λ x, ascent_step h h0





/- ### Part 2 -/

lemma descent_lemma_nat {P : ℕ → Prop} (h : ∃ x, P x) {n : ℕ}
  (h0 : ∀ x, n < x → P x → ∃ x', x' < x ∧ P x') : ∃ x, x ≤ n ∧ P x :=
suffices ∀ N : ℕ, n ≤ N → (∃ x, x ≤ N ∧ P x) → (∃ x, x ≤ n ∧ P x),
from exists.elim h $ λ x h, (le_total x n).elim
  (λ h1, ⟨x, h1, h⟩) (λ h1, this x h1 ⟨x, le_refl x, h⟩),
λ N h1, nat.le_induction id (λ N h1, implies.trans $ λ h2, exists.elim h2 $ λ x h3,
  (le_or_lt x N).elim (λ h4, ⟨x, h4, h3.2⟩) (λ h4, exists.elim (h0 x (h1.trans_lt h4) h3.2) $
    λ x' h5, ⟨x', nat.le_of_lt_succ $ h5.1.trans_le h3.1, h5.2⟩)) N h1

lemma descent_lemma {P : ℤ → Prop} (h : ∀ x, P x → P (|x|)) (h0 : ∃ x, P x)
  {n : ℕ} (h1 : ∀ x : ℤ, n < x.nat_abs → P x → ∃ x' : ℤ, x'.nat_abs < x.nat_abs ∧ P x') :
  ∃ x : ℤ, x.nat_abs ≤ n ∧ P x :=
suffices ∃ x : ℕ, x ≤ n ∧ P x, from exists.elim this $ λ x this, ⟨x, this⟩,
descent_lemma_nat
  (exists.elim h0 $ λ x h0, ⟨x.nat_abs, cast (congr_arg P x.abs_eq_nat_abs) (h x h0)⟩)
  (λ x h2 h3, exists.elim (h1 x h2 h3) $ λ x' h4,
    ⟨x'.nat_abs, h4.1, cast (congr_arg P x'.abs_eq_nat_abs) (h x' h4.2)⟩)

lemma nice_abs_left {k a x y : ℤ} (h : nice k a x y) : nice k a (|x|) y :=
  (congr_arg2 _ rfl $ congr_arg2 _ rfl $ sq_abs x).trans h

lemma nice_sub_formula {k a x y : ℤ} (h : nice k a x y) :
  nice k a ((2 * k + 1) * |x| - 2 * (k + 1) * |y|) (2 * k * |x| - (2 * k + 1) * |y|) :=
suffices nice k a ((2 * k + 1) * |x| + 2 * (k + 1) * (-|y|)) (2 * k * |x| + (2 * k + 1) * (-|y|)),
from cast (congr_arg2 _ ((congr_arg _ $ mul_neg _ _).trans (sub_eq_add_neg _ _).symm)
  ((congr_arg _ $ mul_neg _ _).trans (sub_eq_add_neg _ _).symm)) this,
main_nice_lemma $ nice_abs_left $
  (congr_arg2 _ (congr_arg _ $ (neg_sq _).trans (sq_abs _)) rfl).trans h

lemma descent_step {k a : ℤ} (h : 0 ≤ k) (h0 : 0 < a) {x : ℤ} (h1 : a.nat_abs.sqrt < x.nat_abs)
  (h2 : ∃ y, nice k a x y) : ∃ x' : ℤ, x'.nat_abs < x.nat_abs ∧ ∃ y, nice k a x' y :=
begin
  cases h2 with y h2,
  refine ⟨(2 * k + 1) * |x| - 2 * (k + 1) * |y|, _,
    2 * k * |x| - (2 * k + 1) * |y|, nice_sub_formula h2⟩,
  rw [nat.sqrt_lt, ← sq, ← int.nat_abs_pow, int.nat_abs_lt_iff_mul_self_lt,
      ← abs_lt_iff_mul_self_lt, abs_sq, abs_of_pos h0] at h1,
  rw [int.nat_abs_lt_iff_mul_self_lt, ← abs_lt_iff_mul_self_lt, abs_lt],
  have h3 : 0 < k + 1 := int.lt_add_one_of_le h,
  have h4 : 0 < (2 : ℤ) := two_pos,
  split,

  ---- `-|x| < (2k + 1) |x| - (2k + 2) |y|`
  { rw [neg_lt_sub_iff_lt_add', ← add_one_mul, add_assoc, ← bit0, ← mul_add_one],
    refine mul_lt_mul_of_pos_left _ (mul_pos h4 h3),
    rwa [← sq_lt_sq, ← mul_lt_mul_left h3, eq_add_of_sub_eq h2,
         add_one_mul, add_comm, add_lt_add_iff_left] },

  ---- `(2k + 1) |x| - (2k + 2) |y| < |x|`
  { rw [sub_lt_comm, ← sub_one_mul, add_sub_cancel, mul_assoc, mul_assoc],
    refine (mul_lt_mul_left h4).mpr (abs_lt_of_sq_lt_sq' _ $ mul_nonneg h3.le $ abs_nonneg y).2,
    rw [mul_pow, sq_abs, mul_pow, sq_abs, sq, mul_assoc, sq (k + 1), mul_assoc],
    exact mul_lt_mul'' (lt_add_one k) (lt_of_sub_pos $ h0.trans_eq h2.symm)
      h (mul_nonneg h $ sq_nonneg x) }
end



/-- Final solution, part 2 -/
theorem final_solution_part2 {k a : ℤ} (h : 0 ≤ k) (h0 : 0 < a) (h1 : ∃ x y, nice k a x y) :
  ∃ x : ℤ, x ^ 2 ≤ a ∧ ∃ y, nice k a x y :=
suffices ∃ x : ℤ, x.nat_abs ≤ a.nat_abs.sqrt ∧ ∃ y, nice k a x y,
from exists.elim this $ λ x h2, ⟨x, by rwa [nat.le_sqrt, ← sq, ← int.nat_abs_pow,
  int.nat_abs_le_iff_mul_self_le, ← abs_le_iff_mul_self_le, abs_sq, abs_of_pos h0] at h2⟩,
descent_lemma (λ x h2, exists.elim h2 $ λ y h2, ⟨y, nice_abs_left h2⟩) h1 (λ x, descent_step h h0)

end IMO2016N5
end IMOSL
