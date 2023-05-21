import algebra.hom.ring

/-!
# Explicit construction of 𝔽₃

In this file, we explicitly construct the field of 3 elements.
We prove just the necessary properties for the purpose of the main problem.
We won't even prove that it is a field or a decidable type; just a ring.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₃
| 𝔽₃0 : 𝔽₃
| 𝔽₃1 : 𝔽₃
| 𝔽₃2 : 𝔽₃





namespace 𝔽₃

protected def repr : 𝔽₃ → string
| 𝔽₃0 := "0"
| 𝔽₃1 := "1"
| 𝔽₃2 := "2"

instance : has_repr 𝔽₃ := ⟨𝔽₃.repr⟩



protected def add : 𝔽₃ → 𝔽₃ → 𝔽₃
| 𝔽₃0 x := x
| x 𝔽₃0 := x
| 𝔽₃1 𝔽₃1 := 𝔽₃2
| 𝔽₃1 𝔽₃2 := 𝔽₃0
| 𝔽₃2 𝔽₃1 := 𝔽₃0
| 𝔽₃2 𝔽₃2 := 𝔽₃1

protected def sub : 𝔽₃ → 𝔽₃ → 𝔽₃
| x 𝔽₃0 := x
| 𝔽₃0 𝔽₃1 := 𝔽₃2
| 𝔽₃0 𝔽₃2 := 𝔽₃1
| 𝔽₃1 𝔽₃1 := 𝔽₃0
| 𝔽₃1 𝔽₃2 := 𝔽₃2
| 𝔽₃2 𝔽₃1 := 𝔽₃1
| 𝔽₃2 𝔽₃2 := 𝔽₃0

protected def neg : 𝔽₃ → 𝔽₃ 
| 𝔽₃0 := 𝔽₃0
| 𝔽₃1 := 𝔽₃2
| 𝔽₃2 := 𝔽₃1

protected def mul : 𝔽₃ → 𝔽₃ → 𝔽₃
| 𝔽₃0 x := 𝔽₃0
| 𝔽₃1 x := x
| 𝔽₃2 𝔽₃0 := 𝔽₃0
| 𝔽₃2 𝔽₃1 := 𝔽₃2
| 𝔽₃2 𝔽₃2 := 𝔽₃1

instance : has_zero 𝔽₃ := ⟨𝔽₃0⟩
instance : has_one 𝔽₃ := ⟨𝔽₃1⟩
instance : has_add 𝔽₃ := ⟨𝔽₃.add⟩
instance : has_sub 𝔽₃ := ⟨𝔽₃.sub⟩
instance : has_neg 𝔽₃ := ⟨𝔽₃.neg⟩
instance : has_mul 𝔽₃ := ⟨𝔽₃.mul⟩



protected lemma add_comm : ∀ x y : 𝔽₃, x + y = y + x
| 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 := rfl

protected lemma add_assoc : ∀ x y z : 𝔽₃, x + y + z = x + (y + z)
| 𝔽₃0 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃2 := rfl

protected lemma add_zero : ∀ x : 𝔽₃, x + 0 = x
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

protected lemma zero_add (x : 𝔽₃) : 0 + x = x :=
  (𝔽₃.add_comm 0 x).trans (𝔽₃.add_zero x)

protected lemma add_left_neg : ∀ x : 𝔽₃, -x + x = 0
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

instance : add_comm_group 𝔽₃ :=
{ add_comm := 𝔽₃.add_comm,
  add_assoc := 𝔽₃.add_assoc,
  add_zero := 𝔽₃.add_zero,
  zero_add := 𝔽₃.zero_add,
  add_left_neg := 𝔽₃.add_left_neg,
  .. 𝔽₃.has_add,
  .. 𝔽₃.has_zero,
  .. 𝔽₃.has_neg }



protected lemma mul_comm : ∀ x y : 𝔽₃, x * y = y * x
| 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 := rfl

protected lemma mul_assoc : ∀ x y z : 𝔽₃, x * y * z = x * (y * z)
| 𝔽₃0 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃2 := rfl

protected lemma mul_one : ∀ x : 𝔽₃, x * 1 = x
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

protected lemma one_mul (x : 𝔽₃) : 1 * x = x :=
  (𝔽₃.mul_comm 1 x).trans (𝔽₃.mul_one x)

instance : comm_monoid 𝔽₃ :=
{ mul_comm := 𝔽₃.mul_comm,
  mul_assoc := 𝔽₃.mul_assoc,
  one_mul := 𝔽₃.one_mul,
  mul_one := 𝔽₃.mul_one,
  .. 𝔽₃.has_mul,
  .. 𝔽₃.has_one }



protected lemma mul_add : ∀ x y z : 𝔽₃, x * (y + z) = x * y + x * z
| 𝔽₃0 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 𝔽₃2 := rfl

protected lemma add_mul (x y z : 𝔽₃) : (x + y) * z = x * z + y * z :=
  (𝔽₃.mul_comm _ z).trans $ (𝔽₃.mul_add z x y).trans $
    congr_arg2 𝔽₃.add (𝔽₃.mul_comm z x) (𝔽₃.mul_comm z y)

instance : ring 𝔽₃ :=
{ left_distrib := 𝔽₃.mul_add,
  right_distrib := 𝔽₃.add_mul,
  .. 𝔽₃.add_comm_group,
  .. 𝔽₃.comm_monoid }





section cast

section general

variables {R : Type*} [add_group_with_one R]

def cast : 𝔽₃ → R
| 𝔽₃0 := 0
| 𝔽₃1 := 1
| 𝔽₃2 := -1

instance : has_coe_t 𝔽₃ R := ⟨𝔽₃.cast⟩

lemma cast_zero : (𝔽₃0 : R) = 0 := rfl

lemma cast_one : (𝔽₃1 : R) = 1 := rfl

end general


section ring

variables {R : Type*} [ring R]

lemma cast_mul : ∀ x y : 𝔽₃, ((x * y : 𝔽₃) : R) = x * y
| 𝔽₃0 x := (zero_mul ↑x).symm
| 𝔽₃1 x := (one_mul ↑x).symm
| 𝔽₃2 𝔽₃0 := (mul_zero (-1)).symm
| 𝔽₃2 𝔽₃1 := (mul_one (-1)).symm
| 𝔽₃2 𝔽₃2 := eq.symm $ (neg_mul_neg _ _).trans (mul_one 1)

variable (h : (3 : R) = 0)
include h

lemma cast_add : ∀ x y : 𝔽₃, ((x + y : 𝔽₃) : R) = x + y
| 𝔽₃0 x := (congr_arg cast x.zero_add).trans (zero_add ↑x).symm
| x 𝔽₃0 := (congr_arg cast x.add_zero).trans (add_zero ↑x).symm
| 𝔽₃1 𝔽₃1 := eq.symm (eq_neg_of_add_eq_zero_left h)
| 𝔽₃1 𝔽₃2 := (add_neg_self 1).symm
| 𝔽₃2 𝔽₃1 := (neg_add_self 1).symm
| 𝔽₃2 𝔽₃2 := eq_add_neg_of_add_eq (eq_neg_of_add_eq_zero_left h)

def cast_hom : 𝔽₃ →+* R :=
  ⟨cast, cast_one, cast_mul, cast_zero, cast_add h⟩

variable (h0 : (1 : R) ≠ 0)
include h0

lemma cast_hom_eq_zero_imp : ∀ x : 𝔽₃, cast_hom h x = 0 → x = 0
| 𝔽₃0 := λ _, rfl
| 𝔽₃1 := λ h1, absurd h1 h0
| 𝔽₃2 := λ h1, absurd (neg_eq_zero.mp h1) h0

lemma cast_hom_injective : function.injective (cast_hom h) :=
  (injective_iff_map_eq_zero $ 𝔽₃.cast_hom h).mpr (cast_hom_eq_zero_imp h h0)

end ring

end cast

end 𝔽₃

end IMO2012A5
end IMOSL
