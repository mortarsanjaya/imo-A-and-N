import IMO2018.A7.A7_general analysis.mean_inequalities

/-! # IMO 2018 A7 -/

namespace IMOSL
namespace IMO2018A7

open finset function real

noncomputable def target_sum (q : ℝ) (n : ℕ) (a : ℕ → ℝ) :=
  (range n).sum (λ i, (a i / (a (i + 1) + q)) ^ ((3 : ℕ)⁻¹ : ℝ))

def is_answer (p q : ℝ) (n : ℕ) : ℝ → Prop :=
  is_greatest (target_sum q n '' {a | (∀ i, 0 ≤ a i) ∧ (range n).sum a = n • p ∧ a.periodic n})





/-! ### Cauchy-Schwarz inequality on multiple sums -/

section cauchy_schwarz

variables {ι : Type*} [decidable_eq ι]

lemma real_cauchy_schwarz_two_sqrt {x y : ι → ℝ} {S : finset ι}
  (hx : ∀ i, i ∈ S → 0 ≤ x i) (hy : ∀ i, i ∈ S → 0 ≤ y i) :
  S.sum (λ i, (x i * y i).sqrt) ^ 2 ≤ S.sum x * S.sum y :=
  cauchy_schwarz hx hy $ λ i h, (sq_sqrt $ mul_nonneg (hx i h) (hy i h)).le

lemma real_cauchy_schwarz_four {x y z w a : ι → ℝ} {S : finset ι}
  (hx : ∀ i, i ∈ S → 0 ≤ x i) (hy : ∀ i, i ∈ S → 0 ≤ y i) (hz : ∀ i, i ∈ S → 0 ≤ z i)
  (hw : ∀ i, i ∈ S → 0 ≤ w i) (h : ∀ i, i ∈ S → a i ^ 4 ≤ x i * y i * z i * w i) :
  S.sum a ^ 4 ≤ S.sum x * S.sum y * S.sum z * S.sum w :=
have h0 : ∀ i, i ∈ S → 0 ≤ x i * y i := λ i h0, mul_nonneg (hx i h0) (hy i h0),
have h1 : ∀ i, i ∈ S → 0 ≤ z i * w i := λ i h1, mul_nonneg (hz i h1) (hw i h1),
have h2 : S.sum a ^ 2 ≤ S.sum (λ i, (x i * y i).sqrt) * S.sum (λ i, (z i * w i).sqrt),
  from cauchy_schwarz (λ i _, sqrt_nonneg _) (λ i _, sqrt_nonneg _) $
    λ i h3, (sqrt_mul (h0 i h3) _).le.trans' $ le_sqrt_of_sq_le $
      (pow_mul (a i) 2 2).ge.trans $ (h i h3).trans_eq $ mul_assoc _ _ _,
(pow_four_le_pow_two_of_pow_two_le h2).trans $ (mul_pow _ _ 2).trans_le $
  (mul_assoc _ _ _).ge.trans' $ mul_le_mul (real_cauchy_schwarz_two_sqrt hx hy)
    (real_cauchy_schwarz_two_sqrt hz hw) (sq_nonneg _) $
      mul_nonneg (sum_nonneg hx) (sum_nonneg hy)

lemma real_cauchy_schwarz_three {x y z a : ι → ℝ} {S : finset ι}
  (hx : ∀ i, i ∈ S → 0 ≤ x i) (hy : ∀ i, i ∈ S → 0 ≤ y i) (hz : ∀ i, i ∈ S → 0 ≤ z i)
  (ha : ∀ i, i ∈ S → 0 ≤ a i) (h : ∀ i, i ∈ S → a i ^ 3 ≤ x i * y i * z i) :
  S.sum a ^ 3 ≤ S.sum x * S.sum y * S.sum z :=
(sum_nonneg ha).eq_or_gt.elim
---- Case 1: `∑ a(i) = 0`
(λ h0, h0.symm ▸ (zero_pow $ nat.succ_pos 2 : (0 : ℝ) ^ 3 = 0).symm ▸
  mul_nonneg (mul_nonneg (sum_nonneg hx) (sum_nonneg hy)) (sum_nonneg hz))
---- Case 2: `∑ a(i) > 0`
(λ h0, (mul_le_mul_right h0).mp $ (pow_succ' _ _).symm.trans_le $
  real_cauchy_schwarz_four hx hy hz ha $ λ i h1, (pow_succ' _ _).trans_le $
  mul_le_mul (h i h1) (le_refl _) (ha i h1) $
  mul_nonneg (mul_nonneg (hx i h1) (hy i h1)) (hz i h1))

end cauchy_schwarz





/-! ### Upper Bound -/

section upper_bound

lemma le_nsmul_cube_root_of_cube_le
  {x : ℝ} {y : ℝ} {n : ℕ} (h : 0 ≤ y) (h0 : x ^ 3 ≤ (n : ℝ) ^ 3 * y) :
  x ≤ n • y ^ ((3 : ℕ)⁻¹ : ℝ) :=
le_of_pow_le_pow 3 (nsmul_nonneg (rpow_nonneg_of_nonneg h _) n) (nat.succ_pos 2) $
  let Y := y ^ ((3 : ℕ)⁻¹ : ℝ) in (nsmul_eq_mul n Y).symm ▸ (mul_pow (n : ℝ) Y 3).symm ▸
    (rpow_nat_inv_pow_nat h (nat.succ_ne_zero 2)).symm ▸ h0

variables {q : ℝ} (h : 0 < q) {a : ℕ → ℝ} (h0 : ∀ i, 0 ≤ a i)
include h h0

lemma target_sum_cauchy_schwarz' (n : ℕ) :
  target_sum q n a ^ 3 ≤ (range n).sum (λ k, a k / (a k + q))
    * (range n).sum (λ k, 1 / (a (k + 1) + q)) * ((range n).sum (λ i, a i + q)) :=
let h1 : ∀ i, 0 < a i + q := λ i, add_pos_of_nonneg_of_pos (h0 i) h,
  h2 : ∀ i, 0 ≤ a i / (a (i + 1) + q) := λ i, div_nonneg (h0 i) (h1 _).le in
real_cauchy_schwarz_three
(λ i _, div_nonneg (h0 i) (h1 i).le)
(λ i _, one_div_nonneg.mpr (h1 _).le)
(λ i _, (h1 i).le)
(λ i _, rpow_nonneg_of_nonneg (h2 i) _)
(λ i _, (rpow_nat_inv_pow_nat (h2 i) $ nat.succ_ne_zero 2).trans_le $
  (mul_right_comm _ _ _).ge.trans_eq' $ (div_mul_cancel (a i) (h1 i).ne.symm).symm ▸
  div_eq_mul_one_div _ _)

lemma target_sum_cauchy_schwarz {n : ℕ} (h1 : a.periodic n) :
  target_sum q n a ^ 3 ≤ (range n).sum (λ k, a k / (a k + q))
    * (range n).sum (λ k, 1 / (a k + q)) * ((range n).sum (λ i, a i + q)) :=
suffices (range n).sum (λ k, 1 / (a (k + 1) + q)) = (range n).sum (λ k, 1 / (a k + q)),
  from this ▸ target_sum_cauchy_schwarz' h h0 n,
add_left_injective (1 / (a 0 + q)) $ (sum_range_succ' (λ i, 1 / (a i + q)) n).symm.trans $
  h1 0 ▸ n.zero_add.symm ▸ sum_range_succ _ _

lemma target_sum_upper_bound_range_even {n : ℕ} (h1 : a.periodic (2 * n))
  {p : ℝ} (h2 : (range (2 * n)).sum a = (2 * n) • p) (h3 : 0 ≤ p) :
  target_sum q (2 * n) a ≤ n • (2 * ((p + q) / q)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
let h4 := mul_nonneg (zero_lt_two' ℝ).le (div_nonneg (add_nonneg h3 h.le) h.le) in
le_nsmul_cube_root_of_cube_le h4 $ (target_sum_cauchy_schwarz h h0 h1).trans $
  let h5 := card_range (2 * n) in special_sum_triple_mul_card_even
    h (λ i _, h0 i) (h2.trans $ congr_arg2 _ h5.symm rfl) h5

lemma target_sum_upper_bound_sum_a_small'
  {n : ℕ} (h1 : a.periodic n) (h2 : (range n).sum a ≤ n • q) :
  target_sum q n a ≤ n • ((range n).sum a / ((range n).sum a + n • q)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
let X := (range n).sum a, h4 : 0 ≤ X := sum_nonneg (λ i _, h0 i) in
le_nsmul_cube_root_of_cube_le (div_nonneg h4 $ add_nonneg h4 $ h4.trans h2) $
  let h5 := card_range n in (target_sum_cauchy_schwarz h h0 h1).trans $
    (special_sum_triple_mul_le_of_sum_a h (λ i _, h0 i)
      (h2.trans_eq $ congr_arg2 _ h5.symm rfl)).trans_eq $
    h5.symm ▸ rfl

lemma target_sum_upper_bound_sum_a_small
  {n : ℕ} (h1 : a.periodic n) {p : ℝ} (h2 : (range n).sum a = n • p) (h3 : p ≤ q) :
  target_sum q n a ≤ n • (p / (p + q)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
(eq_or_ne n 0).elim
(λ h4, h4.symm ▸ (sum_range_zero _).trans_le (zero_nsmul _).ge)
(λ h4, suffices (range n).sum a / ((range n).sum a + n • q) = p / (p + q),
  from this ▸ target_sum_upper_bound_sum_a_small' h h0 h1
    (h2.trans_le $ nsmul_le_nsmul_of_le_right h3 n),
h2.symm ▸ nsmul_add p q n ▸ (nsmul_eq_mul n p).symm ▸
  (nsmul_eq_mul n (p + q)).symm ▸ mul_div_mul_left _ _ (nat.cast_ne_zero.mpr h4))

end upper_bound





/-! ### Construction for `p ≥ q` case -/

lemma sq_div_cube_root {a b : ℝ} (h : 0 ≤ a) (h0 : 0 ≤ b) :
  (a ^ 2 / b) ^ ((3 : ℕ)⁻¹ : ℝ) = a / (a * b) ^ ((3 : ℕ)⁻¹ : ℝ) :=
let X : 3 ≠ 0 := nat.succ_ne_zero 2 in h.eq_or_lt.elim
(λ h, h ▸ (sq (0 : ℝ)).symm ▸ (zero_mul (0 : ℝ)).symm ▸ (zero_div b).symm ▸
  (zero_rpow $ inv_ne_zero $ nat.cast_ne_zero.mpr X).trans (zero_div _).symm)
(λ h1, mul_div_mul_left (a ^ 2) b h1.ne.symm ▸ pow_succ a 2 ▸
  (div_rpow (pow_nonneg h 3) (mul_nonneg h h0) _).trans
  (congr_arg2 _ (pow_nat_rpow_nat_inv h X) rfl))

lemma target_sum_two_construction' {u v : ℝ} (h : 0 ≤ u) (h0 : 0 ≤ v) :
  (u ^ 2 / (v * (u + v))) ^ ((3 : ℕ)⁻¹ : ℝ) + (v ^ 2 / (u * (u + v))) ^ ((3 : ℕ)⁻¹ : ℝ)
    = ((u + v) ^ 2 / (u * v)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
let h1 := add_nonneg h h0 in
  (sq_div_cube_root h $ mul_nonneg h0 h1).symm ▸ 
  (sq_div_cube_root h0 $ mul_nonneg h h1).symm ▸
  (sq_div_cube_root h1 $ mul_nonneg h h0).symm ▸
  mul_left_comm u v (u + v) ▸ mul_assoc u v (u + v) ▸
  mul_comm (u + v) (u * v) ▸ (add_div _ _ _).symm

lemma target_sum_two_construction
  {u v p q : ℝ} (h : 0 ≤ u) (h0 : 0 ≤ v) (h1 : u ^ 2 + v ^ 2 = 2 * p) (h2 : u * v = q) :
  (u ^ 2 / (v ^ 2 + q)) ^ ((3 : ℕ)⁻¹ : ℝ) + (v ^ 2 / (u ^ 2 + q)) ^ ((3 : ℕ)⁻¹ : ℝ)
    = (2 * ((p + q) / q)) ^ ((3 : ℕ)⁻¹ : ℝ) :=
let h3 : v ^ 2 + u * v = v * (u + v) := (sq v).symm ▸ add_mul v u v ▸ add_comm u v ▸ mul_comm _ _,
  h4 : u ^ 2 + u * v = u * (u + v) := (sq u).symm ▸ (mul_add u u v).symm in
mul_div_assoc 2 (p + q) q ▸ (mul_add 2 p q).symm ▸ h1 ▸ h2 ▸ mul_assoc 2 u v ▸ add_sq' u v ▸
  h3.symm ▸ h4.symm ▸ target_sum_two_construction' h h0

lemma exists_uv_target_sum_greatest {p q : ℝ} (h : 0 ≤ q) (h0 : q ≤ p) :
  ∃ u v : ℝ, (0 ≤ u ∧ 0 ≤ v) ∧ (u ^ 2 + v ^ 2 = 2 * p ∧ u * v = q) :=
---- First reduce to finding `u, v : ℝ` for `4p` and `2q`
suffices ∃ u v : ℝ, (0 ≤ u ∧ 0 ≤ v) ∧ (u ^ 2 + v ^ 2 = 2 * (2 * p) ∧ u * v = 2 * q),
  from exists.elim this $ λ u this, exists.elim this $ λ v this,
    ⟨u / sqrt 2, v / sqrt 2,
      let h1 := sqrt_nonneg 2 in ⟨div_nonneg this.1.1 h1, div_nonneg this.1.2 h1⟩,
      let h1 := zero_lt_two' ℝ, h2 := sq_sqrt h1.le in
        ⟨let h3 : ∀ x : ℝ, (x / sqrt 2) ^ 2 = x ^ 2 / 2 :=
          λ x, (div_pow _ _ 2).trans $ h2.symm ▸ rfl in
          (congr_arg2 _ (h3 _) (h3 _)).trans $ (add_div _ _ _).symm.trans $
            this.2.1.symm ▸ mul_div_cancel_left _ h1.ne.symm,
        (div_mul_div_comm _ _ _ _).trans $ (congr_arg2 _ this.2.2 (sq _).symm).trans $
          h2.symm ▸ mul_div_cancel_left _ h1.ne.symm⟩⟩,
---- Now find `u, v : ℝ` for `4p` and `2q`
let h1 := sub_nonneg_of_le h0, h2 := (sub_le_self p h).trans (le_add_of_nonneg_right h),
  h3 := sq_sqrt (h1.trans h2), h4 := sq_sqrt h1 in
⟨(p + q).sqrt + (p - q).sqrt, (p + q).sqrt - (p - q).sqrt,
⟨add_nonneg (p + q).sqrt_nonneg (p - q).sqrt_nonneg, sub_nonneg_of_le $ sqrt_le_sqrt h2⟩,
(congr_arg2 _ (add_sq' _ _) (sub_sq' _ _)).trans $ (add_add_sub_cancel _ _ _).trans $
  (two_mul _).symm.trans $ congr_arg2 _ rfl $ (congr_arg2 _ h3 h4).trans $
  (add_add_sub_cancel _ _ _).trans (two_mul p).symm,
(sq_sub_sq _ _).symm.trans $ (congr_arg2 _ h3 h4).trans $
  (add_sub_sub_cancel _ _ _).trans (two_mul q).symm⟩

lemma target_sum_cond (q x y : ℝ) (n : ℕ) :
  target_sum q (2 * n) (λ i, cond i.bodd x y)
    = n • ((x / (y + q)) ^ ((3 : ℕ)⁻¹ : ℝ) + (y / (x + q)) ^ ((3 : ℕ)⁻¹ : ℝ)) :=
suffices ∀ i : ℕ, (cond i.bodd x y / (cond (i + 1).bodd x y + q)) ^ ((3 : ℕ)⁻¹ : ℝ)
    = cond i.bodd ((x / (y + q)) ^ ((3 : ℕ)⁻¹ : ℝ)) ((y / (x + q)) ^ ((3 : ℕ)⁻¹ : ℝ)),
  from (sum_congr rfl $ λ i _, this i).trans $ sum_cond_two_mul _ _ _,
suffices ∀ b : bool, (cond b x y / (cond (!b) x y + q)) ^ ((3 : ℕ)⁻¹ : ℝ)
    = cond b ((x / (y + q)) ^ ((3 : ℕ)⁻¹ : ℝ)) ((y / (x + q)) ^ ((3 : ℕ)⁻¹ : ℝ)),
  from λ i, i.bodd_succ.symm ▸ this i.bodd,
λ b, match b with | tt := rfl | ff := rfl end





/-! ### Final solution -/

/-- Final solution, case `p ≥ q` -/
theorem final_solution_case_p_ge_q {p q : ℝ} (h : 0 < q) (h0 : q ≤ p) (n : ℕ) :
  is_answer p q (2 * n) (n • (2 * ((p + q) / q)) ^ ((3 : ℕ)⁻¹ : ℝ)) :=
⟨exists.elim (exists_uv_target_sum_greatest h.le h0) $ λ u h1, exists.elim h1 $ λ v h1,
  ⟨λ i, cond i.bodd (u ^ 2) (v ^ 2),
    ⟨λ i, le_cond (sq_nonneg u) (sq_nonneg v) _,
    (sum_cond_two_mul _ _ _).trans $ h1.2.1.symm ▸
      (two_mul p).symm ▸ two_nsmul p ▸ (mul_nsmul' p 2 n).symm,
    n.mul_comm 2 ▸ periodic.nat_mul (cond_period_two _ _) n⟩,
    target_sum_two_construction h1.1.1 h1.1.2 h1.2.1 h1.2.2 ▸ target_sum_cond q _ _ n⟩,
λ r h1, exists.elim h1 $ λ a h1, h1.2.ge.trans $
  target_sum_upper_bound_range_even h h1.1.1 h1.1.2.2 h1.1.2.1 (h.le.trans h0)⟩

/-- Final solution, case `p ≤ q` -/
theorem final_solution_case_p_le_q {p q : ℝ} (h : 0 < q) (h0 : 0 ≤ p) (h1 : p ≤ q) (n : ℕ) :
  is_answer p q n (n • (p / (p + q)) ^ ((3 : ℕ)⁻¹ : ℝ)) :=
⟨let h2 := (card_range n).symm in ⟨λ _, p,
  ⟨λ _, h0, (sum_const _).trans $ h2 ▸ rfl, λ _, rfl⟩,
  (sum_const $ (p / (p + q)) ^ ((3 : ℕ)⁻¹ : ℝ)).trans $ h2 ▸ rfl⟩,
λ r h2, exists.elim h2 $ λ a h2, h2.2.ge.trans $
  target_sum_upper_bound_sum_a_small h h2.1.1 h2.1.2.2 h2.1.2.1 h1⟩

end IMO2018A7
end IMOSL
