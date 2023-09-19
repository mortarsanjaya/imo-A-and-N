import algebra.hom.ring

/-!
# Explicit construction of ℤ₄

In this file, we explicitly construct the ring `ℤ/4ℤ`.
We prove just the necessary properties for the purpose of the main problem.
Unfortunately, the author chooses to use the notaion `ℤ₄` just for the sake of short naming.
-/

namespace IMOSL
namespace IMO2012A5

inductive ℤ₄
| ℤ₄0 : ℤ₄
| ℤ₄1 : ℤ₄
| ℤ₄2 : ℤ₄
| ℤ₄3 : ℤ₄





namespace ℤ₄

protected def repr : ℤ₄ → string
| ℤ₄0 := "0"
| ℤ₄1 := "1"
| ℤ₄2 := "2"
| ℤ₄3 := "3"

instance : has_repr ℤ₄ := ⟨ℤ₄.repr⟩



protected def add : ℤ₄ → ℤ₄ → ℤ₄
| ℤ₄0 x := x
| ℤ₄1 ℤ₄0 := ℤ₄1
| ℤ₄1 ℤ₄1 := ℤ₄2
| ℤ₄1 ℤ₄2 := ℤ₄3
| ℤ₄1 ℤ₄3 := ℤ₄0
| ℤ₄2 ℤ₄0 := ℤ₄2
| ℤ₄2 ℤ₄1 := ℤ₄3
| ℤ₄2 ℤ₄2 := ℤ₄0
| ℤ₄2 ℤ₄3 := ℤ₄1
| ℤ₄3 ℤ₄0 := ℤ₄3
| ℤ₄3 ℤ₄1 := ℤ₄0
| ℤ₄3 ℤ₄2 := ℤ₄1
| ℤ₄3 ℤ₄3 := ℤ₄2

protected def neg : ℤ₄ → ℤ₄ 
| ℤ₄0 := ℤ₄0
| ℤ₄1 := ℤ₄3
| ℤ₄2 := ℤ₄2
| ℤ₄3 := ℤ₄1

protected def mul : ℤ₄ → ℤ₄ → ℤ₄
| ℤ₄0 x := ℤ₄0
| ℤ₄1 x := x
| ℤ₄2 ℤ₄0 := ℤ₄0
| ℤ₄2 ℤ₄1 := ℤ₄2
| ℤ₄2 ℤ₄2 := ℤ₄0
| ℤ₄2 ℤ₄3 := ℤ₄2
| ℤ₄3 ℤ₄0 := ℤ₄0
| ℤ₄3 ℤ₄1 := ℤ₄3
| ℤ₄3 ℤ₄2 := ℤ₄2
| ℤ₄3 ℤ₄3 := ℤ₄1

instance : has_zero ℤ₄ := ⟨ℤ₄0⟩
instance : has_one ℤ₄ := ⟨ℤ₄1⟩
instance : has_add ℤ₄ := ⟨ℤ₄.add⟩
instance : has_neg ℤ₄ := ⟨ℤ₄.neg⟩
instance : has_mul ℤ₄ := ⟨ℤ₄.mul⟩



protected lemma add_zero : ∀ x : ℤ₄, x + 0 = x
| ℤ₄0 := rfl
| ℤ₄1 := rfl
| ℤ₄2 := rfl
| ℤ₄3 := rfl

protected lemma zero_add (x : ℤ₄) : 0 + x = x := rfl

protected lemma add_comm : ∀ x y : ℤ₄, x + y = y + x
| ℤ₄0 x := x.add_zero.symm
| x ℤ₄0 := x.add_zero
| ℤ₄1 ℤ₄1 := rfl
| ℤ₄1 ℤ₄2 := rfl
| ℤ₄1 ℤ₄3 := rfl
| ℤ₄2 ℤ₄1 := rfl
| ℤ₄2 ℤ₄2 := rfl
| ℤ₄2 ℤ₄3 := rfl
| ℤ₄3 ℤ₄1 := rfl
| ℤ₄3 ℤ₄2 := rfl
| ℤ₄3 ℤ₄3 := rfl

protected lemma add_assoc : ∀ x y z : ℤ₄, x + y + z = x + (y + z)
| ℤ₄0 y z := rfl
| x ℤ₄0 z := congr_arg (+ z) x.add_zero
| x y ℤ₄0 := (x + y).add_zero.trans $ congr_arg (has_add.add x) y.add_zero.symm
| ℤ₄1 ℤ₄1 ℤ₄1 := rfl
| ℤ₄1 ℤ₄1 ℤ₄2 := rfl
| ℤ₄1 ℤ₄1 ℤ₄3 := rfl
| ℤ₄1 ℤ₄2 ℤ₄1 := rfl
| ℤ₄1 ℤ₄2 ℤ₄2 := rfl
| ℤ₄1 ℤ₄2 ℤ₄3 := rfl
| ℤ₄1 ℤ₄3 ℤ₄1 := rfl
| ℤ₄1 ℤ₄3 ℤ₄2 := rfl
| ℤ₄1 ℤ₄3 ℤ₄3 := rfl
| ℤ₄2 ℤ₄1 ℤ₄1 := rfl
| ℤ₄2 ℤ₄1 ℤ₄2 := rfl
| ℤ₄2 ℤ₄1 ℤ₄3 := rfl
| ℤ₄2 ℤ₄2 ℤ₄1 := rfl
| ℤ₄2 ℤ₄2 ℤ₄2 := rfl
| ℤ₄2 ℤ₄2 ℤ₄3 := rfl
| ℤ₄2 ℤ₄3 ℤ₄1 := rfl
| ℤ₄2 ℤ₄3 ℤ₄2 := rfl
| ℤ₄2 ℤ₄3 ℤ₄3 := rfl
| ℤ₄3 ℤ₄1 ℤ₄1 := rfl
| ℤ₄3 ℤ₄1 ℤ₄2 := rfl
| ℤ₄3 ℤ₄1 ℤ₄3 := rfl
| ℤ₄3 ℤ₄2 ℤ₄1 := rfl
| ℤ₄3 ℤ₄2 ℤ₄2 := rfl
| ℤ₄3 ℤ₄2 ℤ₄3 := rfl
| ℤ₄3 ℤ₄3 ℤ₄1 := rfl
| ℤ₄3 ℤ₄3 ℤ₄2 := rfl
| ℤ₄3 ℤ₄3 ℤ₄3 := rfl

protected lemma add_left_neg : ∀ x : ℤ₄, -x + x = 0
| ℤ₄0 := rfl
| ℤ₄1 := rfl
| ℤ₄2 := rfl
| ℤ₄3 := rfl

instance : add_comm_group ℤ₄ :=
{ add_comm := ℤ₄.add_comm,
  add_assoc := ℤ₄.add_assoc,
  add_zero := ℤ₄.add_zero,
  zero_add := ℤ₄.zero_add,
  add_left_neg := ℤ₄.add_left_neg,
  .. ℤ₄.has_add,
  .. ℤ₄.has_zero,
  .. ℤ₄.has_neg }



protected lemma mul_one : ∀ x : ℤ₄, x * 1 = x
| ℤ₄0 := rfl
| ℤ₄1 := rfl
| ℤ₄2 := rfl
| ℤ₄3 := rfl

protected lemma one_mul (x : ℤ₄) : 1 * x = x := rfl

protected lemma mul_comm : ∀ x y : ℤ₄, x * y = y * x
| ℤ₄1 x := x.mul_one.symm
| x ℤ₄1 := x.mul_one
| ℤ₄0 ℤ₄0 := rfl
| ℤ₄0 ℤ₄2 := rfl
| ℤ₄0 ℤ₄3 := rfl
| ℤ₄2 ℤ₄0 := rfl
| ℤ₄2 ℤ₄2 := rfl
| ℤ₄2 ℤ₄3 := rfl
| ℤ₄3 ℤ₄0 := rfl
| ℤ₄3 ℤ₄2 := rfl
| ℤ₄3 ℤ₄3 := rfl

protected lemma mul_assoc : ∀ x y z : ℤ₄, x * y * z = x * (y * z)
| ℤ₄0 y z := rfl
| ℤ₄1 y z := rfl
| ℤ₄2 ℤ₄0 z := rfl
| ℤ₄2 ℤ₄1 z := rfl
| ℤ₄3 ℤ₄0 z := rfl
| ℤ₄3 ℤ₄1 z := rfl
| ℤ₄2 ℤ₄2 ℤ₄0 := rfl
| ℤ₄2 ℤ₄2 ℤ₄1 := rfl
| ℤ₄2 ℤ₄2 ℤ₄2 := rfl
| ℤ₄2 ℤ₄2 ℤ₄3 := rfl
| ℤ₄2 ℤ₄3 ℤ₄0 := rfl
| ℤ₄2 ℤ₄3 ℤ₄1 := rfl
| ℤ₄2 ℤ₄3 ℤ₄2 := rfl
| ℤ₄2 ℤ₄3 ℤ₄3 := rfl
| ℤ₄3 ℤ₄2 ℤ₄0 := rfl
| ℤ₄3 ℤ₄2 ℤ₄1 := rfl
| ℤ₄3 ℤ₄2 ℤ₄2 := rfl
| ℤ₄3 ℤ₄2 ℤ₄3 := rfl
| ℤ₄3 ℤ₄3 ℤ₄0 := rfl
| ℤ₄3 ℤ₄3 ℤ₄1 := rfl
| ℤ₄3 ℤ₄3 ℤ₄2 := rfl
| ℤ₄3 ℤ₄3 ℤ₄3 := rfl

instance : comm_monoid ℤ₄ :=
{ mul_comm := ℤ₄.mul_comm,
  mul_assoc := ℤ₄.mul_assoc,
  one_mul := ℤ₄.one_mul,
  mul_one := ℤ₄.mul_one,
  .. ℤ₄.has_mul,
  .. ℤ₄.has_one }



protected lemma mul_add : ∀ x y z : ℤ₄, x * (y + z) = x * y + x * z
| ℤ₄0 y z := rfl
| ℤ₄1 y z := rfl
| ℤ₄2 ℤ₄0 z := rfl
| ℤ₄2 ℤ₄1 ℤ₄0 := rfl
| ℤ₄2 ℤ₄1 ℤ₄1 := rfl
| ℤ₄2 ℤ₄1 ℤ₄2 := rfl
| ℤ₄2 ℤ₄1 ℤ₄3 := rfl
| ℤ₄2 ℤ₄2 ℤ₄0 := rfl
| ℤ₄2 ℤ₄2 ℤ₄1 := rfl
| ℤ₄2 ℤ₄2 ℤ₄2 := rfl
| ℤ₄2 ℤ₄2 ℤ₄3 := rfl
| ℤ₄2 ℤ₄3 ℤ₄0 := rfl
| ℤ₄2 ℤ₄3 ℤ₄1 := rfl
| ℤ₄2 ℤ₄3 ℤ₄2 := rfl
| ℤ₄2 ℤ₄3 ℤ₄3 := rfl
| ℤ₄3 ℤ₄0 z := rfl
| ℤ₄3 ℤ₄1 ℤ₄0 := rfl
| ℤ₄3 ℤ₄1 ℤ₄1 := rfl
| ℤ₄3 ℤ₄1 ℤ₄2 := rfl
| ℤ₄3 ℤ₄1 ℤ₄3 := rfl
| ℤ₄3 ℤ₄2 ℤ₄0 := rfl
| ℤ₄3 ℤ₄2 ℤ₄1 := rfl
| ℤ₄3 ℤ₄2 ℤ₄2 := rfl
| ℤ₄3 ℤ₄2 ℤ₄3 := rfl
| ℤ₄3 ℤ₄3 ℤ₄0 := rfl
| ℤ₄3 ℤ₄3 ℤ₄1 := rfl
| ℤ₄3 ℤ₄3 ℤ₄2 := rfl
| ℤ₄3 ℤ₄3 ℤ₄3 := rfl

protected lemma add_mul (x y z : ℤ₄) : (x + y) * z = x * z + y * z :=
  (ℤ₄.mul_comm _ z).trans $ (ℤ₄.mul_add z x y).trans $
    congr_arg2 ℤ₄.add (ℤ₄.mul_comm z x) (ℤ₄.mul_comm z y)

instance : comm_ring ℤ₄ :=
{ left_distrib := ℤ₄.mul_add,
  right_distrib := ℤ₄.add_mul,
  .. ℤ₄.add_comm_group,
  .. ℤ₄.comm_monoid }





section cast

section general

variables {R : Type*} [add_group_with_one R]

def cast : ℤ₄ → R
| ℤ₄0 := 0
| ℤ₄1 := 1
| ℤ₄2 := 2
| ℤ₄3 := -1

instance : has_coe_t ℤ₄ R := ⟨ℤ₄.cast⟩

lemma cast_zero : (ℤ₄0 : R) = 0 := rfl

lemma cast_one : (ℤ₄1 : R) = 1 := rfl

end general


section ring

variables {R : Type*} [ring R] (h : (4 : R) = 0)
include h

lemma cast_add : ∀ x y : ℤ₄, ((x + y : ℤ₄) : R) = x + y
| ℤ₄0 x := (zero_add ↑x).symm
| x ℤ₄0 := x.add_zero.symm ▸ (add_zero ↑x).symm
| ℤ₄1 ℤ₄1 := rfl
| ℤ₄1 ℤ₄2 := neg_eq_of_add_eq_zero_right $ (add_assoc 1 1 2).symm.trans h
| ℤ₄1 ℤ₄3 := (add_neg_self 1).symm
| ℤ₄2 ℤ₄1 := neg_eq_of_add_eq_zero_left $ (add_assoc 2 1 1).trans h
| ℤ₄2 ℤ₄2 := h.symm
| ℤ₄2 ℤ₄3 := (add_neg_cancel_right 1 1).symm
| ℤ₄3 ℤ₄1 := (neg_add_self 1).symm
| ℤ₄3 ℤ₄2 := (neg_add_cancel_left 1 1).symm
| ℤ₄3 ℤ₄3 := (eq_neg_of_add_eq_zero_left h).trans (neg_add 1 1)

lemma cast_mul : ∀ x y : ℤ₄, ((x * y : ℤ₄) : R) = x * y
| ℤ₄0 x := (zero_mul ↑x).symm
| ℤ₄1 x := (one_mul ↑x).symm
| x ℤ₄1 := x.mul_one.symm ▸ (mul_one ↑x).symm
| ℤ₄2 ℤ₄0 := (mul_zero 2).symm
| ℤ₄2 ℤ₄2 := h.symm.trans (mul_two 2).symm
| ℤ₄2 ℤ₄3 := (eq_neg_of_add_eq_zero_left h).trans (mul_neg_one 2).symm
| ℤ₄3 ℤ₄0 := (mul_zero (-1)).symm
| ℤ₄3 ℤ₄2 := (eq_neg_of_add_eq_zero_left h).trans (neg_one_mul 2).symm
| ℤ₄3 ℤ₄3 := (one_mul 1).symm.trans (neg_mul_neg 1 1).symm

def cast_hom : ℤ₄ →+* R :=
  ⟨cast, cast_one, cast_mul h, cast_zero, cast_add h⟩

variables (h0 : (2 : R) ≠ 0)
include h0

lemma cast_hom_eq_zero_imp : ∀ x : ℤ₄, cast_hom h x = 0 → x = 0
| ℤ₄0 := λ _, rfl
| ℤ₄1 := λ h2, false.elim $ h0 $ h2.symm ▸ (congr_arg2 has_add.add h2 h2).trans (add_zero 0)
| ℤ₄2 := λ h2, absurd h2 h0
| ℤ₄3 := λ h2, false.elim $ h0 $ let h3 := neg_eq_zero.mp h2 in 
    (congr_arg2 has_add.add h3 h3).trans (add_zero 0)

lemma cast_hom_injective : function.injective (cast_hom h) :=
  (injective_iff_map_eq_zero $ cast_hom h).mpr (cast_hom_eq_zero_imp h h0)

end ring

end cast

end ℤ₄

end IMO2012A5
end IMOSL
