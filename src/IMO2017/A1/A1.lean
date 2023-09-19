import algebra.big_operators.order algebra.big_operators.ring data.rat.lemmas

/-! # IMO 2017 A1 -/

namespace IMOSL
namespace IMO2017A1

variables {R : Type*} [linear_ordered_comm_semiring R]

lemma bernoulli_ineq_aux {x y : R} (h : 0 ≤ x) (h0 : 0 ≤ y) (n : ℕ) :
  y ^ n.succ * (n.succ.succ * x + y) ≤ y ^ n * (n.succ * x + y) * (x + y) :=
begin
  rw [pow_succ', mul_right_comm, mul_assoc, mul_assoc],
  refine mul_le_mul_of_nonneg_left _ (pow_nonneg h0 n),
  rw [nat.cast_succ, add_one_mul, add_right_comm, mul_add, add_mul, add_comm,
      add_le_add_iff_right, add_mul, mul_comm, le_add_iff_nonneg_left],
  exact mul_nonneg (mul_nonneg n.succ.cast_nonneg h) h
end

lemma bernoulli_ineq {x y : R} (h : 0 ≤ x) (h0 : 0 ≤ y) :
  ∀ n : ℕ, y ^ n * (n.succ * x + y) ≤ (x + y) ^ n.succ
| 0 := by rw [pow_zero, one_mul, nat.cast_one, one_mul, pow_one]
| (n+1) := (bernoulli_ineq_aux h h0 n).trans $
    (mul_le_mul_of_nonneg_right (bernoulli_ineq n) $ add_nonneg h h0).trans_eq
    (pow_succ' (x + y) n.succ).symm

lemma bernoulli_ineq_strict {x y : R} (h : 0 < x) (h0 : 0 ≤ y) :
  ∀ n : ℕ, y ^ n.succ * (n.succ.succ * x + y) < (x + y) ^ n.succ.succ
| 0 := by rw [pow_one, mul_add, nat.cast_two, add_sq, mul_comm,
    add_assoc, ← sq, lt_add_iff_pos_left]; exact pow_pos h 2
| (n+1) := (bernoulli_ineq_aux h.le h0 n.succ).trans_lt $
  (mul_lt_mul_of_pos_right (bernoulli_ineq_strict n) $ add_pos_of_pos_of_nonneg h h0).trans_eq
  (pow_succ' (x + y) n.succ.succ).symm

lemma bernoulli_eq_case {x y : R} (h : 0 < x) (h0 : 0 ≤ y) :
  ∀ {n : ℕ}, y ^ n * (n.succ * x + y) = (x + y) ^ n.succ → n = 0
| 0 := λ _, rfl
| (n+1) := λ h1, absurd h1 $ (bernoulli_ineq_strict h h0 n).ne

lemma special_ineq {x : R} (h : 0 ≤ x) :
  ∀ {a : ℕ}, 0 < a → (a : R) ^ a * (x + 1) ≤ (x + a) ^ a
| 0 := λ h0, absurd h0 (lt_irrefl 0)
| (a+1) := λ _, by rw [pow_succ', mul_assoc, mul_add_one];
    exact bernoulli_ineq h a.succ.cast_nonneg a

lemma special_ineq_eq_case {x : R} (h : 0 < x) :
  ∀ {a : ℕ}, (a : R) ^ a * (x + 1) = (x + a) ^ a → a = 1
| 0 := λ h0, by rw [pow_zero, pow_zero, one_mul, add_left_eq_self] at h0;
    exact absurd h0 (ne_of_gt h)
| (a+1) := λ h0, by rw [pow_succ', mul_assoc, mul_add_one] at h0;
    exact add_left_eq_self.mpr (bernoulli_eq_case h a.succ.cast_nonneg h0)



open multiset

/-- For some reason, this DOES NOT exist in mathlib at time of writing -/
lemma multiset_prod_pow_eq_pow_sum {α : Type*} [comm_monoid α] (x : α) (S : multiset ℕ) :
  (S.map $ has_pow.pow x).prod = x ^ S.sum :=
  multiset.induction_on S
    (by rw [multiset.map_zero, prod_zero, sum_zero, pow_zero])
    (λ n T h, by rw [map_cons, prod_cons, h, ← pow_add, sum_cons])
    
lemma multiset_prod_map_pow_eq_pow_sum_map {ι α : Type*} [comm_monoid α] (f : ι → ℕ)
  (x : α) (S : multiset ι) : (S.map $ λ i, x ^ f i).prod = x ^ (S.map f).sum :=
  by rw [← multiset_prod_pow_eq_pow_sum, map_map]

/-- If `0 < n` for all `n : S`, then `0 < ∏ S`. -/
lemma multiset_prod_pos {S : multiset R} : (∀ r : R, r ∈ S → 0 < r) → 0 < S.prod :=
  multiset.induction_on S
    (λ _, one_pos.trans_eq prod_zero.symm)
    (λ c T h h0, lt_of_eq_of_lt' (prod_cons c T).symm $
      mul_pos (h0 c $ mem_cons_self c T) (h $ λ r h1, h0 r $ mem_cons_of_mem h1))

/-- If `0 ≤ f ≤ g` on `S`, then `∏_{i ∈ S} f(i) ≤ ∏_{i ∈ S} g(i)`. -/
lemma ring_map_prod_le_map_prod {ι : Type*} {f g : ι → R} {S : multiset ι} :
  (∀ i, i ∈ S → 0 ≤ f i) → (∀ i, i ∈ S → f i ≤ g i) → (S.map f).prod ≤ (S.map g).prod :=
multiset.induction_on S
  (λ _ _, by rw [multiset.map_zero, multiset.map_zero])
  (λ j T h1 h2 h3, by rw [map_cons, map_cons, prod_cons, prod_cons];
    have h4 := mem_cons_self j T; exact mul_le_mul
      (h3 j h4)
      (h1 (λ i h5, h2 i $ mem_cons_of_mem h5) (λ i h5, h3 i $ mem_cons_of_mem h5))
      (prod_nonneg $ λ t h5, exists.elim (mem_map.mp h5) $
        λ i h5, (h2 i $ mem_cons_of_mem h5.1).trans_eq h5.2)
      ((h2 j h4).trans $ h3 j h4))

/-- If `0 < f ≤ g` on `S` and `∏_{i ∈ S} f(i) = ∏_{i ∈ S} g(i)`,
  then `f(i) = g(i)` for all `i ∈ S`. -/
lemma all_eq_of_pos_le_of_prod_eq {ι : Type*} {f g : ι → R} {S : multiset ι}
  (h : ∀ i, i ∈ S → 0 < f i) (h0 : ∀ i, i ∈ S → f i ≤ g i)
  (h1 : (S.map f).prod = (S.map g).prod) {j : ι} (h2 : j ∈ S) : f j = g j :=
begin
  contrapose h1; apply ne_of_lt,
  rcases multiset.exists_cons_of_mem h2 with ⟨T, rfl⟩,
  rw [map_cons, map_cons, prod_cons, prod_cons],
  exact mul_lt_mul ((h0 j h2).lt_of_ne h1)
    (ring_map_prod_le_map_prod (λ i h3, (h i $ mem_cons_of_mem h3).le) $
      λ i h3, h0 i $ mem_cons_of_mem h3)
    (multiset_prod_pos $ λ r h3, exists.elim (mem_map.mp h3) $
      λ i h3, (h i $ mem_cons_of_mem h3.1).trans_eq h3.2)
    ((h j h2).le.trans (h0 j h2))
end

lemma all_eq_of_pos_le_of_prod_pow_self_eq {f g : ℕ → R} {S : multiset ℕ}
  (h : ∀ n, n ∈ S → 0 < f n) (h0 : ∀ n, n ∈ S → f n ≤ g n)
  (a : ℕ → ℕ) (h1 : ∀ n, n ∈ S → 0 < a n)
  (h2 : (S.map $ λ n, f n ^ a n).prod = (S.map $ λ n, g n ^ a n).prod)
  {n : ℕ} (h3 : n ∈ S) : f n = g n :=
le_antisymm (h0 n h3) $ le_of_pow_le_pow (a n) (h n h3).le (h1 n h3) $ ge_of_eq $
  let h0 := λ N h4, pow_le_pow_of_le_left (h N h4).le (h0 N h4) (a N),
    h := λ N h4, pow_pos (h N h4) (a N), h4 := all_eq_of_pos_le_of_prod_eq h h0 h2 h3 in h4


variables {S : multiset ℕ} {k : ℕ} (h : (S.map $ λ s : ℕ, (s : ℚ)⁻¹).sum = k)
include h

lemma k_mul_prod_eq : k * S.prod = (S.map $ has_div.div S.prod).sum :=
begin
  rw [← int.coe_nat_inj', ← rat.coe_int_inj, int.cast_coe_nat, nat.cast_mul, ← h,
      int.cast_coe_nat, ← sum_map_mul_right, nat.cast_multiset_sum, map_map],
  refine congr_arg sum (map_congr rfl $ λ s h0, _),
  rw [function.comp_app, ← div_eq_inv_mul, rat.coe_nat_div S.prod s (dvd_prod h0)]
end





/-- Final solution -/
theorem final_solution (h0 : ∀ n : ℕ, n ∈ S → 0 < n) {x : R} (h1 : 0 < x) :
  (S.prod : R) * (x + 1) ^ k = (S.map $ λ s : ℕ, x + s).prod →
    ∀ {n : ℕ}, n ∈ S → n = 1 :=
let h2 : ∀ {n : ℕ}, n ∈ S → n ∣ S.prod := λ n, dvd_prod in
suffices
  (map (λ (s : ℕ), x + s) S).prod ^ S.prod =
    (S.map $ λ n : ℕ, ((x + n) ^ n) ^ (S.prod / n)).prod ∧ 
  (S.map $ λ n : ℕ, ((n : R) ^ n * (x + 1)) ^ (S.prod / n)).prod
    = (S.prod * (x + 1) ^ k) ^ S.prod,
from λ h3 n h4, special_ineq_eq_case h1 $
  let h5 : ∀ n, n ∈ S → 0 < ↑n ^ n * (x + 1) :=
    λ N h5, mul_pos (pow_pos (nat.cast_pos.mpr $ h0 N h5) N) (add_pos h1 one_pos) in
  all_eq_of_pos_le_of_prod_pow_self_eq h5
    (λ N h6, special_ineq h1.le (h0 N h6)) (has_div.div S.prod)
    (λ N h6, nat.div_pos (nat.le_of_dvd (multiset_prod_pos h0) (h2 h6)) (h0 N h6))
    (this.2.trans $ (congr_arg2 has_pow.pow h3 rfl).trans this.1) h4,
⟨prod_map_pow.symm.trans $ congr_arg multiset.prod $ map_congr rfl $ λ n h3,
  by rw [← pow_mul, nat.mul_div_cancel' (h2 h3)],
begin
  conv_lhs { congr, congr, funext, rw [mul_pow, ← pow_mul] },
  rw [prod_map_mul, multiset_prod_map_pow_eq_pow_sum_map, ← k_mul_prod_eq h,
      mul_pow, nat.cast_multiset_prod, ← prod_map_pow],
  exact congr_arg2 has_mul.mul (congr_arg _ $ map_congr rfl $ λ n h3,
    congr_arg2 has_pow.pow rfl $ nat.mul_div_cancel' $ h2 h3) (pow_mul _ _ _)
end⟩

end IMO2017A1
end IMOSL
