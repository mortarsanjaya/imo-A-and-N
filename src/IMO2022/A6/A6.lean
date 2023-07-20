import linear_algebra.basis data.rat.floor

/-! # IMO 2022 A6 -/

namespace IMOSL
namespace IMO2022A6

def infectious {V : Type*} [add_monoid V] (f : V → V) :=
  ∀ x y : V, f (x + f y) = f x + f y

def good (V : Type*) [add_comm_group V] [module ℚ V] (q : ℚ) :=
  ∀ f : V → V, infectious f → ∃ z : V, f z = q • z





/- ### Step 1: `1 + n^{-1}` is good for any `V` -/

section step1

variables (V : Type*) [add_comm_group V] [module ℚ V]

lemma map_smul_map_zero_of_infectious {f : V → V} (h : infectious f) (k : ℤ) :
  f (k • f 0) = (k + 1) • f 0 :=
int.induction_on k
---- `f(0) = f(0)`
(by rw [zero_zsmul, zero_add, one_zsmul])
---- `f(k f(0)) = (k + 1) f(0) → f((k + 1) f(0)) = (k + 2) f(0)`
(λ k h0, by rw [add_one_zsmul, h, h0, ← add_one_zsmul])
---- `f(k f(0)) = (k + 1) f(0) → f((k + 1) f(0)) = (k + 2) f(0)`
(λ k h0, by rwa [← add_sub_right_comm, sub_one_zsmul _ (-(k : ℤ) + 1),
  eq_add_neg_iff_add_eq, ← h, ← add_one_zsmul, sub_add_cancel])

lemma one_add_inv_is_good {n : ℤ} (h : n ≠ 0) : good V (1 + (n : ℚ)⁻¹) :=
  λ f h0, ⟨(n : ℚ) • f 0, have (n : ℚ) ≠ 0 := int.cast_ne_zero.mpr h,
    by rw [smul_smul, one_add_mul, add_smul, inv_mul_cancel this, int_cast_smul,
      map_smul_map_zero_of_infectious V h0, add_one_zsmul, one_smul]⟩

end step1





/- ### Step 2: Constructions of "bad" infectious functions over `V = ℚ` -/

/-- Extra lemma on the denominator of `n + q` with `n : ℤ`, `q : ℚ` -/
lemma rat_coe_int_add_denom : ∀ (n : ℤ) (q : ℚ), ((n : ℚ) + q).denom = q.denom :=
suffices ∀ (n : ℤ) (q : ℚ), ((n : ℚ) + q).denom ∣ q.denom,
from λ n q, nat.dvd_antisymm (this n q) $ cast (congr_arg2 _ (congr_arg rat.denom $
  by rw [int.cast_neg, neg_add_cancel_left]) rfl) (this (-n) (n + q)),
λ n q, (rat.add_denom_dvd n q).trans $ by rw [rat.coe_int_denom, one_mul]

/-- Note: this function is computable! -/
def rat_bad_fn (q x : ℚ) : ℤ :=
  int.floor x + ite ((q / (1 - q) * int.fract x).denom = 1) 1 0

lemma rat_bad_fn_add_int (q x : ℚ) (n : ℤ) :
  rat_bad_fn q (x + n) = rat_bad_fn q x + n :=
  by rw [rat_bad_fn, rat_bad_fn, int.floor_add_int, add_right_comm, int.fract_add_int]

lemma rat_bad_fn_is_infectious (q : ℚ) : infectious (coe ∘ rat_bad_fn q) :=
  λ x y, (congr_arg coe $ rat_bad_fn_add_int q x _).trans $ int.cast_add _ _


section step2

variables {q : ℚ} (x : ℚ) (h : (rat_bad_fn q x : ℚ) = q • x)
include h

lemma one_sub_ne_zero_of_rat_bad_fn_eq_mul : 1 - q ≠ 0 :=
  λ h0, by rw [rat_bad_fn, h0, div_zero, zero_mul, if_pos rat.denom_zero, int.cast_add,
    ← eq_of_sub_eq_zero h0, one_smul] at h; exact (int.lt_floor_add_one x).ne h.symm

private lemma rat_bad_fn_eq_mul_alt_form :
  q / (1 - q) * int.fract x
    = ite ((q / (1 - q) * int.fract x).denom = 1) (⌊x⌋ + (1 - q)⁻¹) ⌊x⌋ :=
begin
  have h0 := one_sub_ne_zero_of_rat_bad_fn_eq_mul x h,
  nth_rewrite 1 ← int.floor_add_fract x at h,
  rw [smul_eq_mul, mul_add, ← sub_eq_iff_eq_add', rat_bad_fn,
      int.cast_add, add_sub_right_comm, ← one_sub_mul] at h,
  nth_rewrite 0 ← mul_div_right_comm,
  rw [← h, mul_comm, ← add_div' _ _ _ h0, int.cast_ite, div_eq_mul_inv, ite_mul, add_ite],
  refine if_congr (iff.refl _) (congr_arg _ $ one_mul _) (add_right_eq_self.mpr $ zero_mul _)
end

lemma rat_bad_fn_eq_mul_imp : ∃ n : ℤ, n ≠ 0 ∧ q = 1 + (n : ℚ)⁻¹ :=
let h0 := rat_bad_fn_eq_mul_alt_form x h in
(eq_or_ne (q / (1 - q) * int.fract x).denom 1).elim
---- Case 1: `q {x}/(1 - q)` is an integer
(λ h1, begin
  rw if_pos h1 at h0,
  rw [h0, rat_coe_int_add_denom] at h1,
  refine ⟨-(1 - q)⁻¹.num, neg_ne_zero.mpr $ rat.num_ne_zero_of_ne_zero $
    inv_ne_zero (one_sub_ne_zero_of_rat_bad_fn_eq_mul x h), _⟩,
  rwa [← sub_eq_iff_eq_add', eq_comm, inv_eq_iff_eq_inv, int.cast_neg,
       neg_eq_iff_eq_neg, neg_inv, neg_sub, ← rat.denom_eq_one_iff]
end)
---- Case 2: `q {x}/(1 - q)` is not an integer
(λ h1, begin
  rw if_neg h1 at h0,
  rw [h0, rat.coe_int_denom] at h1,
  exact absurd rfl h1
end)

end step2





/- ### Step 3: Generalize to `ℚ`-vector spaces -/

noncomputable def finsupp_rat_bad_fn {α : Type*} (a : α) (q : ℚ) (x : α →₀ ℚ) : α →₀ ℚ :=
  finsupp.single a (rat_bad_fn q $ x a)

lemma finsupp_rat_bad_fn_is_infectious {α : Type*} (a : α) (q : ℚ) :
  infectious (finsupp_rat_bad_fn a q) :=
  λ x y, by iterate 3 { rw finsupp_rat_bad_fn };
    rw [x.add_apply, finsupp.single_eq_same, ← finsupp.single_add];
    exact congr_arg _ (rat_bad_fn_is_infectious q (x a) (y a))

lemma finsupp_rat_bad_fn_eq_mul_imp {α : Type*} {a : α} {q : ℚ} (x : α →₀ ℚ)
  (h0 : finsupp_rat_bad_fn a q x = q • x) : ∃ n : ℤ, n ≠ 0 ∧ q = 1 + (n : ℚ)⁻¹ :=
  rat_bad_fn_eq_mul_imp (x a) $ finsupp.single_eq_same.symm.trans $
    (finsupp.congr_fun h0 a).trans $ x.smul_apply q a


lemma infectious_equiv {V : Type*} [add_comm_group V] [module ℚ V] {f : V → V}
  (h : infectious f) {W : Type*} [add_comm_group W] [module ℚ W] (φ : W ≃ₗ[ℚ] V) :
  infectious (φ.symm ∘ f ∘ φ) :=
  λ x y, by iterate 6 { rw function.comp_app };
    rw [φ.map_add, φ.apply_symm_apply, h, φ.symm.map_add]


lemma good_imp_of_basis_elt (V : Type*) [add_comm_group V] [module ℚ V]
  (ι : Type*) (B : basis ι ℚ V) (i : ι) {q : ℚ} (h : good V q) :
  ∃ n : ℤ, n ≠ 0 ∧ q = 1 + (n : ℚ)⁻¹ :=
begin
  ---- The first line takes more than 0.1s; I don't know why
  cases h _ (infectious_equiv (finsupp_rat_bad_fn_is_infectious i q) B.repr) with x h0,
  rw [function.comp_app, function.comp_app, B.repr.symm_apply_eq, B.repr.map_smul] at h0,
  exact finsupp_rat_bad_fn_eq_mul_imp _ h0
end





/-- Final solution -/
theorem final_solution (V : Type*) [add_comm_group V] [module ℚ V] [nontrivial V] (q : ℚ) :
  good V q ↔ ∃ n : ℤ, n ≠ 0 ∧ q = 1 + (n : ℚ)⁻¹ :=
⟨(basis.of_vector_space ℚ V).index_nonempty.elim $
  λ i, good_imp_of_basis_elt V _ (basis.of_vector_space ℚ V) i,
λ h, exists.elim h $ λ n h, cast (congr_arg _ h.2.symm) $ one_add_inv_is_good V h.1⟩

end IMO2022A6
end IMOSL
