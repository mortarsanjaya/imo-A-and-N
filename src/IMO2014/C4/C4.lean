import
  algebra.big_operators.multiset.basic
  algebra.group.prod
  tactic.norm_num
  extra.fin4

/-! # IMO 2014 C4 -/

namespace IMOSL
namespace IMO2014C4

open multiset

/- ### Weight on `ℕ × ℕ` -/

/-- `(x, y)`-weight of a `multiset (ℕ × ℕ)`. -/
def weight : (ℕ × ℕ) → multiset (ℕ × ℕ) → ℕ
| (x, y) S := (S.map $ λ p : ℕ × ℕ, x ^ p.1 * y ^ p.2).sum

lemma weight_zero (z : ℕ × ℕ) : weight z 0 = 0 :=
match z with | (x, y) := rfl end

lemma weight_cons (x y : ℕ) (v : ℕ × ℕ) (S : multiset (ℕ × ℕ)) :
  weight (x, y) (v ::ₘ S) = x ^ v.1 * y ^ v.2 + weight (x, y) S :=
  (congr_arg multiset.sum $ map_cons _ v S).trans $ sum_cons _ _

lemma weight_add (z : ℕ × ℕ) (S T : multiset (ℕ × ℕ)) :
  weight z (S + T) = weight z S + weight z T :=
match z with | (x, y) :=
  (congr_arg multiset.sum $ multiset.map_add _ S T).trans $ sum_add _ _ end

/-- `(x, y)`-weight of a translated `multiset (ℕ × ℕ)`. -/
lemma weight_translate (x y : ℕ) (v : ℕ × ℕ) (S : multiset (ℕ × ℕ)) :
  weight (x, y) (S.map $ has_add.add v) = (x ^ v.1 * y ^ v.2) * weight (x, y) S :=
  multiset.induction_on S rfl $ λ p S h, by rw [map_cons, weight_cons, prod.fst_add,
    pow_add, prod.snd_add, pow_add, mul_mul_mul_comm, h, ← mul_add, ← weight_cons]





/- ### Base skew-tetrominoes -/

open extra extra.fin4

/-- Base skew-tetrominoes. -/
def base_skew_t4 : fin4 → multiset (ℕ × ℕ)
| i1 := {(0, 0), (1, 0), (1, 1), (2, 1)}
| i2 := {(1, 0), (1, 1), (0, 1), (0, 2)}
| i3 := {(0, 1), (1, 1), (1, 0), (2, 0)}
| i4 := {(0, 0), (0, 1), (1, 1), (1, 2)}

section explicit_base_skew_weight

variables (x y : ℕ)

/-- Weight of base skew-tetromino of type 1. -/
lemma weight_base_skew_t4_i1 :
  weight (x, y) (base_skew_t4 i1) = (1 + x) * (1 + x * y) :=
begin
  rw [weight, base_skew_t4],
  iterate 3 { rw [insert_eq_cons, map_cons, sum_cons] },
  rw [map_singleton, sum_singleton, ← add_assoc, pow_zero, pow_zero, pow_one,
      ← add_mul, pow_one, sq, mul_assoc, ← one_add_mul, ← mul_add]
end

/-- Weight of base skew-tetromino of type 2. -/
lemma weight_base_skew_t4_i2 :
  weight (x, y) (base_skew_t4 i2) = (x + y) * (1 + y) :=
begin
  rw [weight, base_skew_t4],
  iterate 3 { rw [insert_eq_cons, map_cons, sum_cons] },
  rw [map_singleton, sum_singleton, ← add_assoc, pow_zero, pow_one, pow_one,
      ← mul_add, pow_zero, sq, ← mul_assoc, one_mul, ← mul_one_add, ← add_mul]
end

/-- Weight of base skew-tetromino of type 3. -/
lemma weight_base_skew_t4_i3 :
  weight (x, y) (base_skew_t4 i3) = (1 + x) * (y + x) :=
begin
  rw [weight, base_skew_t4],
  iterate 3 { rw [insert_eq_cons, map_cons, sum_cons] },
  rw [map_singleton, sum_singleton, ← add_assoc, pow_zero, pow_one, pow_one,
      ← add_mul, pow_zero, sq, mul_assoc, mul_one, ← one_add_mul, ← mul_add]
end

/-- Weight of base skew-tetromino of type 4. -/
lemma weight_base_skew_t4_i4 :
  weight (x, y) (base_skew_t4 i4) = (1 + x * y) * (1 + y) :=
begin
  rw [weight, base_skew_t4],
  iterate 3 { rw [insert_eq_cons, map_cons, sum_cons] },
  rw [map_singleton, sum_singleton, ← add_assoc, pow_zero, pow_zero, pow_one,
      ← mul_add, pow_one, sq, ← mul_assoc, ← mul_one_add, ← add_mul]
end

end explicit_base_skew_weight





/- ### General skew-tetrominoes -/

/-- Skew-tetrominoes. -/
def skew_t4 (q : fin4 × (ℕ × ℕ)) : multiset (ℕ × ℕ) :=
  (base_skew_t4 q.1).map (has_add.add q.2)

section explicit_weight

variables (x y : ℕ)

/-- Weight of a skew-tetromino with respect to base form. -/
lemma weight_skew_t4_of_base (q : fin4 × (ℕ × ℕ)) :
  weight (x, y) (skew_t4 q) = x ^ q.2.1 * y ^ q.2.2 * weight (x, y) (base_skew_t4 q.1) :=
  weight_translate x y q.2 (base_skew_t4 q.1)

variables (p : ℕ × ℕ)

/-- Weight of a skew-tetromino of type 1. -/
lemma weight_skew_t4_i1 : weight (x, y) (skew_t4 (i1, p)) =
  x ^ p.1 * y ^ p.2 * ((1 + x) * (1 + x * y)) :=
  (weight_skew_t4_of_base x y (i1, p)).trans $
    congr_arg (has_mul.mul _) (weight_base_skew_t4_i1 x y)

/-- Weight of a skew-tetromino of type 2. -/
lemma weight_skew_t4_i2 : weight (x, y) (skew_t4 (i2, p)) =
  x ^ p.1 * y ^ p.2 * ((x + y) * (1 + y)) :=
  (weight_skew_t4_of_base x y (i2, p)).trans $
    congr_arg (has_mul.mul _) (weight_base_skew_t4_i2 x y)

/-- Weight of a skew-tetromino of type 3. -/
lemma weight_skew_t4_i3 : weight (x, y) (skew_t4 (i3, p)) =
  x ^ p.1 * y ^ p.2 * ((1 + x) * (y + x)) :=
  (weight_skew_t4_of_base x y (i3, p)).trans $
    congr_arg (has_mul.mul _) (weight_base_skew_t4_i3 x y)

/-- Weight of a skew-tetromino of type 4. -/
lemma weight_skew_t4_i4 : weight (x, y) (skew_t4 (i4, p)) =
  x ^ p.1 * y ^ p.2 * ((1 + x * y) * (1 + y)) :=
  (weight_skew_t4_of_base x y (i4, p)).trans $
    congr_arg (has_mul.mul _) (weight_base_skew_t4_i4 x y)

end explicit_weight





/- ### Weight of skew-tetrominoes modulo `32` -/

/-- Explicit weight-based skew-tetromino filter. -/
def skew_t4_filter : fin4 → (ℕ × ℕ)
| i1 := (13, 3)
| i2 := (3, 5)
| i3 := (5, 3)
| i4 := (3, 13)

/-- Auxiliary lemma 1 for the weights mod `32` -/
private lemma mod_two_mul_eq_of_bit1_mul {s k n : ℕ} (h : s = bit1 k * n) (u v a b : ℕ) :
  bit1 u ^ a * bit1 v ^ b * s % (n * 2) = n :=
  by rw [mul_comm n, h, ← mul_assoc, nat.mul_mod_mul_right,
    nat.mul_mod, nat.bit1_mod_two, mul_one, nat.mod_mod, nat.mul_mod,
    nat.pow_mod, nat.bit1_mod_two, one_pow, nat.pow_mod, nat.bit1_mod_two,
    one_pow, nat.one_mod, one_mul, nat.one_mod, one_mul]

/-- Weight of skew-tetrominoes modulo `32` under filter.
  (It takes 0.2-0.3s, but this one is a naturally huge proof.) -/
lemma weight_skew_filter_mod_32 (i : fin4) (q : fin4 × (ℕ × ℕ)) :
  weight (skew_t4_filter i) (skew_t4 q) % (16 * 2) = 16 * ite (i = q.1) 1 0 :=
  let h1 : (1 + 13) * (1 + 13 * 3) = 35 * 16 := by norm_num in
match i, q with
| i1, (i1, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i1 _ _ p).trans $
    mod_two_mul_eq_of_bit1_mul h1 _ _ _ _
| i1, (i2, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i2 _ _ p).trans $
  nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨2, by norm_num⟩ _
| i1, (i3, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i3 _ _ p).trans $
  nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨7, by norm_num⟩ _
| i1, (i4, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i4 _ _ p).trans $
  nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨5, by norm_num⟩ _
| i2, (i1, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i1 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨2, by norm_num⟩ _
| i2, (i2, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i2 _ _ p).trans $
    mod_two_mul_eq_of_bit1_mul (by norm_num : _ = 3 * 16) _ _ _ _
| i2, (i3, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i3 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨1, by norm_num⟩ _
| i2, (i4, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i4 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨3, by norm_num⟩ _
| i3, (i1, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i1 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨3, by norm_num⟩ _
| i3, (i2, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i2 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨1, by norm_num⟩ _
| i3, (i3, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i3 _ _ p).trans $
    mod_two_mul_eq_of_bit1_mul (by norm_num : _ = 3 * 16) _ _ _ _
| i3, (i4, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i4 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨2, by norm_num⟩ _
| i4, (i1, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i1 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨5, by norm_num⟩ _
| i4, (i2, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i2 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨7, by norm_num⟩ _
| i4, (i3, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i3 _ _ p).trans $
    nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right ⟨2, by norm_num⟩ _
| i4, (i4, p) := (congr_arg (% (16 * 2)) $ weight_skew_t4_i4 _ _ p).trans $
    mod_two_mul_eq_of_bit1_mul ((mul_comm _ _).trans h1) _ _ _ _
end





/- ### Skew-tetromino partition -/

lemma weight_sum_skew_filter_mod_32 (i : fin4) (P : multiset (fin4 × (ℕ × ℕ))) :
  weight (skew_t4_filter i) (P.map skew_t4).sum % (16 * 2) =
    16 * ((P.map prod.fst).count i % 2) :=
  multiset.induction_on P
    (by rw [multiset.map_zero, sum_zero, weight_zero, multiset.map_zero,
      count_zero, nat.zero_mod, nat.zero_mod, mul_zero])
    (λ S P h, by rw [map_cons, sum_cons, weight_add, nat.add_mod, h,
      weight_skew_filter_mod_32, ← mul_add, nat.mul_mod_mul_left,
      map_cons, count_cons, nat.add_mod_mod, add_comm])


/-- Final solution -/
theorem final_solution {P Q : multiset (fin4 × (ℕ × ℕ))}
  (h : (P.map skew_t4).sum = (Q.map skew_t4).sum) (i : fin4) :
  (P.map prod.fst).count i % 2 = (Q.map prod.fst).count i % 2 :=
  nat.eq_of_mul_eq_mul_left (bit0_pos $ bit0_pos $ bit0_pos $ bit0_pos nat.one_pos) $
    by rw [← weight_sum_skew_filter_mod_32, ← weight_sum_skew_filter_mod_32, h]

end IMO2014C4
end IMOSL
