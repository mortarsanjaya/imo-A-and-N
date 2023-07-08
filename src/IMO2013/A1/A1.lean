import data.matrix.notation algebra.big_operators.fin

/-! # IMO 2013 A1 -/

namespace IMOSL
namespace IMO2013A1

open list matrix
open_locale matrix

/- ### Extra stuffs -/

/-- `![1, 0]` -/
def one_zero_vec (R : Type*) [has_zero R] [has_one R] : fin 2 → R := ![1, 0]

section noncomm_ring

variables {R : Type*} [ring R]

lemma matrix_fin2_mul_vec {R : Type*} [ring R]
  (M : matrix (fin 2) (fin 2) R) (v : fin 2 → R) (b : fin 2) :
  M.mul_vec v b = M b 0 * v 0 + M b 1 * v 1 :=
  vec2_dot_product (M b) v

lemma matrix_fin2_vec_mul {R : Type*} [ring R]
  (v : fin 2 → R) (M : matrix (fin 2) (fin 2) R) (b : fin 2) :
  vec_mul v M b = v 0 * M 0 b + v 1 * M 1 b :=
  vec2_dot_product v _





/- ### Main Definition -/

def f_aux : list R → R × R
| nil := (1, 1)
| (r :: l) := let p := f_aux l in (p.1 + r * p.2, p.1)

lemma f_aux_nil : f_aux (nil : list R) = (1, 1) := rfl

lemma f_aux_cons (r : R) (l : list R) :
  f_aux (r :: l) = ((f_aux l).1 + r * (f_aux l).2, (f_aux l).1) := rfl

/-- The main function -/
def f (l : list R) : R := (f_aux l).1





/- ### Alternative calculation 1 -/

def M (r : R) : matrix (fin 2) (fin 2) R :=
  !![1 + r, -r; r, -r]

def f_aux_alt1 (l : list R) : fin 2 → R :=
  foldr (λ r, (M r).mul_vec) (one_zero_vec R) l

lemma f_aux_alt1_nil : f_aux_alt1 nil = one_zero_vec R := rfl

lemma f_aux_alt1_cons (r : R) (l : list R) :
  f_aux_alt1 (r :: l) = (M r).mul_vec (f_aux_alt1 l) := rfl

lemma f_aux_alt1_prod_description :
  ∀ l : list R, f_aux_alt1 l = (l.map M).prod.mul_vec (one_zero_vec R)
| nil := (one_mul_vec $ one_zero_vec R).symm
| (r :: l) := by rw [map_cons, prod_cons, f_aux_alt1_cons,
    f_aux_alt1_prod_description, mul_vec_mul_vec, mul_eq_mul]

lemma f_aux_matrix_description1 :
  ∀ l : list R, f_aux l = (f_aux_alt1 l 0, f_aux_alt1 l 0 - f_aux_alt1 l 1)
| nil := prod.ext rfl (sub_zero 1).symm
| (r :: l) := begin
  rw [f_aux_cons, f_aux_alt1_cons, f_aux_matrix_description1,
      prod.mk.inj_iff, matrix_fin2_mul_vec, matrix_fin2_mul_vec, M],
  simp only [matrix.head_cons, of_apply, cons_val_one, cons_val_zero]; split,
  rw [one_add_mul, neg_mul, add_assoc, ← sub_eq_add_neg, mul_sub],
  rw [add_sub_add_right_eq_sub, one_add_mul, add_sub_cancel]
end

lemma f_description1 (l : list R) : f l = f_aux_alt1 l 0 :=
  by rw [f, f_aux_matrix_description1]





/- ### Alternative calculation 2 -/

def f_aux_alt2 (l : list R) : fin 2 → R :=
  foldr (λ r v, vec_mul v $ M r) (one_zero_vec R) l

lemma f_aux_alt2_nil : f_aux_alt2 nil = one_zero_vec R := rfl

lemma f_aux_alt2_cons (r : R) (l : list R) :
  f_aux_alt2 (r :: l) = vec_mul (f_aux_alt2 l) (M r) := rfl

lemma f_aux_alt2_prod_description :
  ∀ l : list R, f_aux_alt2 l = vec_mul (one_zero_vec R) (l.reverse.map M).prod
| nil := (vec_mul_one $ one_zero_vec R).symm
| (r :: l) := by rw [f_aux_alt2_cons, reverse_cons, map_append, map_singleton, prod_append,
    prod_singleton, f_aux_alt2_prod_description, vec_mul_vec_mul, mul_eq_mul]

end noncomm_ring



section comm_ring

variables {R : Type*} [comm_ring R]

lemma f_aux_matrix_description2 :
  ∀ l : list R, f_aux l = (f_aux_alt2 l 0, f_aux_alt2 l 0 + f_aux_alt2 l 1)
| nil := prod.ext rfl (add_zero 1).symm
| (r :: l) := begin
  rw [f_aux_cons, f_aux_alt2_cons, f_aux_matrix_description2,
      prod.mk.inj_iff, matrix_fin2_vec_mul, matrix_fin2_vec_mul, M],
  simp only [matrix.head_cons, of_apply, cons_val_one, cons_val_zero]; split,
  rw [mul_comm, add_mul, mul_one_add, add_assoc],
  rw [← add_mul, mul_one_add, add_assoc (f_aux_alt2 l 0),
      ← add_mul, mul_neg, add_neg_cancel_right]
end

lemma f_description2 (l : list R) : f l = f_aux_alt2 l 0 :=
  by rw [f, f_aux_matrix_description2]





/- ### Solution -/

theorem final_solution (l : list R) : f l.reverse = f l :=
  by rw [f_description2, f_aux_alt2_prod_description, reverse_reverse, matrix_fin2_vec_mul,
    f_description1, f_aux_alt1_prod_description, one_zero_vec, matrix_fin2_mul_vec,
    cons_val_one, matrix.head_cons, zero_mul, add_zero, mul_zero, add_zero, mul_comm]

end comm_ring

end IMO2013A1
end IMOSL
