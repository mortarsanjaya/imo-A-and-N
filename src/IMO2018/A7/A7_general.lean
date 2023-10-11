import algebra.big_operators.order algebra.big_operators.ring

/-! # IMO 2018 A7, General properties not reliant on `ℝ` -/

namespace IMOSL
namespace IMO2018A7

open finset
open_locale classical

section comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]

lemma two_sq_mul_le_add_sq (a b : R) : 2 ^ 2 * (a * b) ≤ (a + b) ^ 2 :=
  (add_sq' a b).ge.trans' $ (sq (2 : R)).symm ▸ (mul_assoc 2 2 (a * b)).symm ▸
    mul_assoc 2 a b ▸ (two_mul _).trans_le (add_le_add_right (two_mul_le_add_sq a b) _) 

/-- Cauchy-Schwarz inequality, two variables -/
lemma cauchy_schwarz_two_vars {a b c x y z : R} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hx : 0 ≤ x) (hy : 0 ≤ y) (h : c ^ 2 ≤ a * b) (h0 : z ^ 2 ≤ x * y) :
  (c + z) ^ 2 ≤ (a + x) * (b + y) :=
suffices 2 * (c * z) ≤ a * y + x * b,
  from (add_sq' c z).trans_le $ (add_mul a x (b + y)).symm ▸ (mul_add a b y).symm ▸
    add_comm y b ▸ (mul_add x y b).symm ▸ add_add_add_comm (a * b) (x * y) (a * y) (x * b) ▸
    add_le_add (add_le_add h h0) ((mul_assoc _ _ _).trans_le this),
suffices (2 * (c * z)) ^ 2 ≤ (a * y + x * b) ^ 2,
  from (abs_le_of_sq_le_sq' this $ add_nonneg (mul_nonneg ha hy) (mul_nonneg hx hb)).2,
suffices (c * z) ^ 2 ≤ a * y * (b * x), from (two_sq_mul_le_add_sq _ _).trans' $
  (mul_pow _ _ 2).trans_le $ mul_comm b x ▸ mul_le_mul_of_nonneg_left this (sq_nonneg 2),
(mul_pow c z 2).trans_le $ mul_mul_mul_comm a b y x ▸ mul_comm x y ▸
  mul_le_mul h h0 (sq_nonneg z) (mul_nonneg ha hb)

/-- Cauchy-Schwarz inequality -/
lemma cauchy_schwarz {ι : Type*} [decidable_eq ι] {x y z : ι → R} {S : finset ι} :
  (∀ i, i ∈ S → 0 ≤ x i) → (∀ i, i ∈ S → 0 ≤ y i) → (∀ i, i ∈ S → z i ^ 2 ≤ x i * y i) →
    S.sum z ^ 2 ≤ S.sum x * S.sum y :=
finset.induction_on S
---- Base case: `S = ∅`
(λ h h0 h1, let h2 : ∀ f : ι → R, 0 = (∅ : finset ι).sum f := λ f, sum_empty.symm in
  h2 z ▸ (sq 0).le)
---- Induction step
(λ j S h h0 h1 h2 h3,
  let h4 : ∀ f : ι → R, f j + S.sum f = (insert j S).sum f := λ f, (sum_insert h).symm,
    h5 := mem_insert_self j S, h6 : ∀ i, i ∈ S → i ∈ insert j S := λ i, mem_insert_of_mem,
    h7 : ∀ i, i ∈ S → 0 ≤ x i := λ i h7, h1 i $ h6 i h7,
    h8 : ∀ i, i ∈ S → 0 ≤ y i := λ i h8, h2 i $ h6 i h8 in
    h4 z ▸ h4 x ▸ h4 y ▸ cauchy_schwarz_two_vars (h1 j h5) (h2 j h5) (sum_nonneg h7)
      (sum_nonneg h8) (h3 j h5) (h0 h7 h8 $ λ i h9, h3 i $ h6 i h9))

lemma prod_le_prod_of_add_eq_add {a b c d : R}
  (h : c ≤ d) (h0 : d ≤ b) (h1 : a + b = c + d) : a * b ≤ c * d :=
(eq_sub_of_add_eq h1).symm ▸ (add_sub_right_comm c d b).symm ▸ (add_mul (c - b) d b).symm ▸
  add_le_of_le_sub_right (mul_comm b d ▸ sub_mul c b d ▸
    mul_le_mul_of_nonpos_left h0 (sub_nonpos_of_le $ h.trans h0))

lemma prod_le_prod_of_add_eq_add' {a b c d q : R}
  (h : 0 < q) (h0 : c ≤ q * d) (h1 : d ≤ b) (h2 : a + q * b = c + q * d) : a * b ≤ c * d :=
  (mul_le_mul_left h).mp $ (mul_left_comm q a b).trans_le $ mul_left_comm c q d ▸
    prod_le_prod_of_add_eq_add h0 ((mul_le_mul_left h).mpr h1) h2

end comm_ring



lemma le_cond {α : Type*} [has_le α] {x y z : α} (h : x ≤ y) (h0 : x ≤ z) :
  ∀ b : bool, x ≤ cond b y z
| tt := h
| ff := h0

lemma cond_period_two {α : Type*} (x y : α) (n : ℕ) :
  cond (n + 2).bodd x y = cond n.bodd x y :=
  congr_fun₂ (congr_arg cond $ (n.bodd_add 2).trans $ bxor_ff _) x y



section add_comm_group

variables {G : Type*} [add_comm_monoid G]

lemma sum_add_const {ι : Type*} (S : finset ι) (f : ι → G) (x : G) :
  S.sum (λ i, f i + x) = S.sum f + S.card • x :=
  sum_add_distrib.trans $ congr_arg2 _ rfl (sum_const x)

lemma cond_add_bnot (x y : G) : ∀ b : bool, cond b x y + cond (!b) x y = x + y
| tt := rfl
| ff := add_comm y x

lemma sum_cond_add_two (x y : G) (n : ℕ) :
  (range (n + 2)).sum (λ i, cond i.bodd x y) = (range n).sum (λ i, cond i.bodd x y) + (x + y) :=
  (sum_range_succ _ _).trans $ cond_add_bnot x y n.bodd ▸ n.bodd_succ ▸
    (sum_range_succ (λ i, cond i.bodd x y) n).symm ▸ add_assoc _ _ _

lemma sum_cond_two_mul (x y : G) :
  ∀ n : ℕ, (range (2 * n)).sum (λ i, cond i.bodd x y) = n • (x + y)
| 0 := (sum_range_zero _).trans (zero_nsmul _).symm
| (n+1) := (sum_cond_add_two x y (2 * n)).trans $
    (sum_cond_two_mul n).symm ▸ (succ_nsmul' _ n).symm

end add_comm_group



section field

variables {F : Type*} [linear_ordered_field F] 

/-- The Engel variant of Cauchy-Schwarz inequality -/
lemma cauchy_schwarz_engel
  {ι : Type*} (x y : ι → F) {S : finset ι} (h : ∀ i, i ∈ S → 0 < y i) :
  S.sum x ^ 2 / S.sum y ≤ S.sum (λ i, x i ^ 2 / y i) :=
let h0 : ∀ i, i ∈ S → 0 ≤ y i := λ i h0, (h i h0).le,
  h1 : ∀ i, i ∈ S → 0 ≤ x i ^ 2 / y i := λ i h1, div_nonneg (sq_nonneg _) (h0 i h1) in
div_le_of_nonneg_of_le_mul (sum_nonneg h0) (sum_nonneg h1) $
  cauchy_schwarz h1 h0 (λ i h2, (div_mul_cancel _ (h i h2).ne.symm).ge)

/-- The Engel variant of Cauchy-Schwarz inequality with numerator `1` -/
lemma cauchy_schwarz_engel_num_one
  {ι : Type*} (y : ι → F) {S : finset ι} (h : ∀ i, i ∈ S → 0 < y i) :
  (S.card : F) ^ 2 / S.sum y ≤ S.sum (λ i, 1 / y i) :=
let h0 : S.sum (λ _, (1 : F)) = S.card := (sum_const _).trans (nsmul_one _) in
  (one_pow 2 : (1 : F) ^ 2 = 1) ▸ h0 ▸ cauchy_schwarz_engel _ _ h





/-! ## Problem-specific lemmas -/

variables {ι : Type*} {S : finset ι} {q : F} (h : 0 < q) {a : ι → F} (h0 : ∀ i, i ∈ S → 0 ≤ a i)
include h h0

lemma special_sum_add_eq :
  S.sum (λ i, a i / (a i + q)) + q * S.sum (λ i, 1 / (a i + q)) = S.card :=
suffices ∀ i, i ∈ S → a i / (a i + q) + q * (1 / (a i + q)) = 1,
  from (mul_sum : q * S.sum (λ i, 1 / (a i + q)) = _).symm ▸ sum_add_distrib.symm.trans
    ((sum_congr rfl this).trans $ (sum_const 1).trans $ nsmul_one S.card),
λ i h1, (mul_one_div q (a i + q)).symm ▸ (add_div _ _ _).symm.trans $
  div_self (add_pos_of_nonneg_of_pos (h0 i h1) h).ne.symm

lemma special_sum_mul_le_general :
  (2 ^ 2 * q) * (S.sum (λ i, a i / (a i + q)) * S.sum (λ i, 1 / (a i + q))) ≤ S.card ^ 2 :=
  (mul_assoc _ _ _).trans_le $ special_sum_add_eq h h0 ▸
    mul_left_comm (S.sum (λ i, a i / (a i + q))) q (S.sum (λ i, 1 / (a i + q))) ▸
    two_sq_mul_le_add_sq _ _

lemma special_sum_triple_mul_le_general {p : F} (h1 : S.sum a = S.card • p) :
  (2 ^ 2 * q) *
    (S.sum (λ i, a i / (a i + q)) * S.sum (λ i, 1 / (a i + q)) * S.sum (λ i, a i + q))
    ≤ S.card ^ 3 * (p + q) :=
  (mul_assoc _ _ _).symm.trans_le $ (sum_add_const S a q).symm ▸ (pow_succ' (S.card : F) 2).symm ▸
    (mul_assoc (S.card ^ 2 : F) S.card (p + q)).symm ▸ nsmul_eq_mul S.card (p + q) ▸
    (nsmul_add p q S.card).symm ▸ h1 ▸ mul_le_mul_of_nonneg_right
      (special_sum_mul_le_general h h0) (add_nonneg (sum_nonneg h0) (nsmul_nonneg h.le S.card))

lemma special_sum_triple_mul_card_even
  {p : F} (h1 : S.sum a = S.card • p) {n : ℕ} (h2 : S.card = 2 * n) :
  S.sum (λ i, a i / (a i + q)) * S.sum (λ i, 1 / (a i + q)) * S.sum (λ i, a i + q)
    ≤ n ^ 3 * (2 * ((p + q) / q)) :=
let h3 : (0 : F) < 2 ^ 2 := pow_pos (zero_lt_two' F) 2 in
suffices ((2 * n : ℕ) : F) ^ 3 / 2 ^ 2 = n ^ 3 * 2,
  from ((le_div_iff' $ mul_pos h3 h).mpr $ special_sum_triple_mul_le_general h h0 h1).trans_eq $
    (mul_div_mul_comm _ _ _ _).trans $ h2.symm ▸ this.symm ▸ mul_assoc _ _ _,
(div_eq_iff h3.ne.symm).mpr $ (mul_assoc ((n : F) ^ 3) 2 (2 ^ 2)).symm ▸
  pow_succ (2 : F) 2 ▸ mul_pow (n : F) 2 3 ▸ mul_comm (2 : F) n ▸
  congr_arg2 _ ((nat.cast_mul _ _).trans $ congr_arg2 _ nat.cast_two rfl) rfl 

lemma special_sum_triple_mul_le_of_sum_a (h1 : S.sum a ≤ S.card • q) :
  S.sum (λ i, a i / (a i + q)) * S.sum (λ i, 1 / (a i + q)) * S.sum (λ i, a i + q)
    ≤ S.card ^ 3 * (S.sum a / (S.sum a + S.card • q)) :=
let H := sum_add_const S a q, X := S.sum (λ i, a i + q) in
  H ▸ (sum_nonneg (λ i h2, add_nonneg (h0 i h2) h.le) : 0 ≤ X).eq_or_lt.elim
---- Case 1: `X = 0`
(λ h2, h2 ▸ (mul_zero _).le.trans_eq (mul_eq_zero_of_right _ $ div_zero _).symm)
---- Case 2: `X > 0`
(λ h2, suffices S.sum (λ i, a i / (a i + q)) * S.sum (λ i, 1 / (a i + q))
    ≤ (S.card * S.sum a / X) * (S.card ^ 2 / X),
  from (le_div_iff h2).mp $ this.trans_eq $ (mul_div_mul_comm _ _ _ _).symm.trans $
    mul_right_comm (S.card : F)(S.card ^ 2) (S.sum a) ▸ pow_succ (S.card : F) 2 ▸ 
    (mul_div_right_comm (S.card ^ 3 : F) (S.sum a / X) X).symm ▸ mul_div_mul_comm _ _ _ _,
let Y := (S.card : F), h3 : q * (Y ^ 2 / X) = Y * S.card • q / X :=
  (nsmul_eq_mul S.card q).symm ▸ mul_assoc Y Y q ▸ sq Y ▸
    mul_comm q (Y ^ 2) ▸ (mul_div_assoc q (Y ^ 2) X).symm in
prod_le_prod_of_add_eq_add' h
  (h3.symm ▸ (div_le_div_right h2).mpr (mul_le_mul_of_nonneg_left h1 S.card.cast_nonneg))
  (cauchy_schwarz_engel_num_one _ $ λ i h3, add_pos_of_nonneg_of_pos (h0 i h3) h)
  ((special_sum_add_eq h h0).trans $ h3.symm ▸ add_div (Y * S.sum a) (Y * S.card • q) X ▸
    mul_add Y (S.sum a) (S.card • q) ▸ H ▸ (mul_div_cancel _ h2.ne.symm).symm))

end field

end IMO2018A7
end IMOSL
