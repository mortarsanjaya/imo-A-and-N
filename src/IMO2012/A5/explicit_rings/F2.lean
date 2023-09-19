import algebra.hom.ring

/-!
# Explicit construction of 𝔽₂

In this file, we explicitly construct the field of 2 elements.
We prove just the necessary properties for the purpose of the main problem.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₂
| O : 𝔽₂
| I : 𝔽₂





namespace 𝔽₂

protected def repr : 𝔽₂ → string
| O := "0"
| I := "1"

instance : has_repr 𝔽₂ := ⟨𝔽₂.repr⟩



protected def add : 𝔽₂ → 𝔽₂ → 𝔽₂
| O x := x
| I O := I
| I I := O

protected def mul : 𝔽₂ → 𝔽₂ → 𝔽₂
| O x := O
| I x := x

instance : has_zero 𝔽₂ := ⟨O⟩
instance : has_one 𝔽₂ := ⟨I⟩
instance : has_add 𝔽₂ := ⟨𝔽₂.add⟩
instance : has_neg 𝔽₂ := ⟨id⟩
instance : has_mul 𝔽₂ := ⟨𝔽₂.mul⟩



protected lemma add_zero : ∀ x : 𝔽₂, x + 0 = x
| O := rfl
| I := rfl

protected lemma zero_add (x : 𝔽₂) : 0 + x = x := rfl

protected lemma add_comm : ∀ x y : 𝔽₂, x + y = y + x
| O x := x.add_zero.symm
| I O := rfl
| I I := rfl

protected lemma add_assoc : ∀ x y z : 𝔽₂, x + y + z = x + (y + z)
| O y z := rfl
| I O z := rfl
| I I O := rfl
| I I I := rfl

protected lemma add_left_neg : ∀ x : 𝔽₂, -x + x = 0
| O := rfl
| I := rfl

instance : add_comm_group 𝔽₂ :=
{ add_comm := 𝔽₂.add_comm,
  add_assoc := 𝔽₂.add_assoc,
  add_zero := 𝔽₂.add_zero,
  zero_add := 𝔽₂.zero_add,
  add_left_neg := 𝔽₂.add_left_neg,
  .. 𝔽₂.has_add,
  .. 𝔽₂.has_zero,
  .. 𝔽₂.has_neg }



protected lemma mul_one : ∀ x : 𝔽₂, x * 1 = x
| O := rfl
| I := rfl

protected lemma one_mul (x : 𝔽₂) : 1 * x = x := rfl

protected lemma mul_comm : ∀ x y : 𝔽₂, x * y = y * x
| I x := x.mul_one.symm
| O O := rfl
| O I := rfl

protected lemma mul_assoc : ∀ x y z : 𝔽₂, x * y * z = x * (y * z)
| O y z := rfl
| I y z := rfl

instance : comm_monoid 𝔽₂ :=
{ mul_comm := 𝔽₂.mul_comm,
  mul_assoc := 𝔽₂.mul_assoc,
  one_mul := 𝔽₂.one_mul,
  mul_one := 𝔽₂.mul_one,
  .. 𝔽₂.has_mul,
  .. 𝔽₂.has_one }



protected lemma mul_add : ∀ x y z : 𝔽₂, x * (y + z) = x * y + x * z
| O y z := rfl
| I y z := rfl

protected lemma add_mul : ∀ x y z : 𝔽₂, (x + y) * z = x * z + y * z
| O y z := rfl
| I O z := z.add_zero.symm
| I I O := rfl
| I I I := rfl

instance : ring 𝔽₂ :=
{ left_distrib := 𝔽₂.mul_add,
  right_distrib := 𝔽₂.add_mul,
  .. 𝔽₂.add_comm_group,
  .. 𝔽₂.comm_monoid }





section cast

section general

variables {R : Type*} [add_group_with_one R]

def cast : 𝔽₂ → R
| O := 0
| I := 1

instance : has_coe_t 𝔽₂ R := ⟨𝔽₂.cast⟩

lemma cast_zero : (O : R) = 0 := rfl

lemma cast_one : (I : R) = 1 := rfl

end general


section ring

variables {R : Type*} [ring R]

lemma cast_mul : ∀ x y : 𝔽₂, ((x * y : 𝔽₂) : R) = x * y
| O x := (zero_mul ↑x).symm
| I x := (one_mul ↑x).symm

variable (h : (2 : R) = 0)
include h

lemma cast_add : ∀ x y : 𝔽₂, ((x + y : 𝔽₂) : R) = x + y
| O x := (zero_add ↑x).symm
| I O := (add_zero 1).symm
| I I := h.symm

def cast_hom : 𝔽₂ →+* R :=
  ⟨cast, cast_one, cast_mul, cast_zero, cast_add h⟩

variable (h0 : (1 : R) ≠ 0)
include h0

lemma cast_hom_eq_zero_imp : ∀ x : 𝔽₂, cast_hom h x = 0 → x = 0
| O := λ _, rfl
| I := λ h1, absurd h1 h0

lemma cast_hom_injective : function.injective (cast_hom h) :=
  (injective_iff_map_eq_zero $ cast_hom h).mpr (cast_hom_eq_zero_imp h h0)

end ring

end cast

end 𝔽₂

end IMO2012A5
end IMOSL
