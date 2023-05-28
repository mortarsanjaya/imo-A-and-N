import algebra.hom.ring

/-!
# Explicit construction of 𝔽₄

In this file, we explicitly construct the field of 4 elements.
We prove just the necessary properties for the purpose of the main problem.
We won't even prove that it is a field or a decidable type; just a ring.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₄
| O : 𝔽₄
| I : 𝔽₄
| X : 𝔽₄
| Y : 𝔽₄





namespace 𝔽₄

protected def repr : 𝔽₄ → string
| O := "0"
| I := "1"
| X := "2"
| Y := "3"

instance : has_repr 𝔽₄ := ⟨𝔽₄.repr⟩



protected def add : 𝔽₄ → 𝔽₄ → 𝔽₄
| O x := x
| I O := I
| I I := O
| I X := Y
| I Y := X
| X O := X
| X I := Y
| X X := O
| X Y := I
| Y O := Y
| Y I := X
| Y X := I
| Y Y := O

protected def mul : 𝔽₄ → 𝔽₄ → 𝔽₄
| O x := O
| I x := x
| X O := O
| X I := X
| X X := Y
| X Y := I
| Y O := O
| Y I := Y
| Y X := I
| Y Y := X

instance : has_zero 𝔽₄ := ⟨O⟩
instance : has_one 𝔽₄ := ⟨I⟩
instance : has_add 𝔽₄ := ⟨𝔽₄.add⟩
instance : has_neg 𝔽₄ := ⟨id⟩
instance : has_mul 𝔽₄ := ⟨𝔽₄.mul⟩



protected lemma add_zero : ∀ x : 𝔽₄, x + 0 = x
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

protected lemma zero_add (x : 𝔽₄) : 0 + x = x := rfl

protected lemma add_comm : ∀ x y : 𝔽₄, x + y = y + x
| O x := x.add_zero.symm
| x O := x.add_zero
| I I := rfl
| I X := rfl
| I Y := rfl
| X I := rfl
| X X := rfl
| X Y := rfl
| Y I := rfl
| Y X := rfl
| Y Y := rfl

protected lemma add_assoc : ∀ x y z : 𝔽₄, x + y + z = x + (y + z)
| O y z := rfl
| x O z := congr_arg (+ z) x.add_zero
| x y O := (x + y).add_zero.trans $ congr_arg (has_add.add x) y.add_zero.symm
| I I I := rfl
| I I X := rfl
| I I Y := rfl
| I X I := rfl
| I X X := rfl
| I X Y := rfl
| I Y I := rfl
| I Y X := rfl
| I Y Y := rfl
| X I I := rfl
| X I X := rfl
| X I Y := rfl
| X X I := rfl
| X X X := rfl
| X X Y := rfl
| X Y I := rfl
| X Y X := rfl
| X Y Y := rfl
| Y I I := rfl
| Y I X := rfl
| Y I Y := rfl
| Y X I := rfl
| Y X X := rfl
| Y X Y := rfl
| Y Y I := rfl
| Y Y X := rfl
| Y Y Y := rfl

protected lemma add_left_neg : ∀ x : 𝔽₄, -x + x = 0
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

instance : add_comm_group 𝔽₄ :=
{ add_comm := 𝔽₄.add_comm,
  add_assoc := 𝔽₄.add_assoc,
  add_zero := 𝔽₄.add_zero,
  zero_add := 𝔽₄.zero_add,
  add_left_neg := 𝔽₄.add_left_neg,
  .. 𝔽₄.has_add,
  .. 𝔽₄.has_zero,
  .. 𝔽₄.has_neg }



protected lemma mul_one : ∀ x : 𝔽₄, x * 1 = x
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

protected lemma one_mul (x : 𝔽₄) : 1 * x = x := rfl

protected lemma mul_comm : ∀ x y : 𝔽₄, x * y = y * x
| I x := x.mul_one.symm
| x I := x.mul_one
| O O := rfl
| O X := rfl
| O Y := rfl
| X O := rfl
| X X := rfl
| X Y := rfl
| Y O := rfl
| Y X := rfl
| Y Y := rfl

protected lemma mul_assoc : ∀ x y z : 𝔽₄, x * y * z = x * (y * z)
| O y z := rfl
| I y z := rfl
| X O z := rfl
| X I z := rfl
| Y O z := rfl
| Y I z := rfl
| X X O := rfl
| X X I := rfl
| X X X := rfl
| X X Y := rfl
| X Y O := rfl
| X Y I := rfl
| X Y X := rfl
| X Y Y := rfl
| Y X O := rfl
| Y X I := rfl
| Y X X := rfl
| Y X Y := rfl
| Y Y O := rfl
| Y Y I := rfl
| Y Y X := rfl
| Y Y Y := rfl

instance : comm_monoid 𝔽₄ :=
{ mul_comm := 𝔽₄.mul_comm,
  mul_assoc := 𝔽₄.mul_assoc,
  one_mul := 𝔽₄.one_mul,
  mul_one := 𝔽₄.mul_one,
  .. 𝔽₄.has_mul,
  .. 𝔽₄.has_one }



protected lemma mul_add : ∀ x y z : 𝔽₄, x * (y + z) = x * y + x * z
| O y z := rfl
| I y z := rfl
| X O z := rfl
| X I O := rfl
| X I I := rfl
| X I X := rfl
| X I Y := rfl
| X X O := rfl
| X X I := rfl
| X X X := rfl
| X X Y := rfl
| X Y O := rfl
| X Y I := rfl
| X Y X := rfl
| X Y Y := rfl
| Y O z := rfl
| Y I O := rfl
| Y I I := rfl
| Y I X := rfl
| Y I Y := rfl
| Y X O := rfl
| Y X I := rfl
| Y X X := rfl
| Y X Y := rfl
| Y Y O := rfl
| Y Y I := rfl
| Y Y X := rfl
| Y Y Y := rfl

protected lemma add_mul (x y z : 𝔽₄) : (x + y) * z = x * z + y * z :=
  (𝔽₄.mul_comm _ z).trans $ (𝔽₄.mul_add z x y).trans $
    congr_arg2 𝔽₄.add (𝔽₄.mul_comm z x) (𝔽₄.mul_comm z y)

instance : comm_ring 𝔽₄ :=
{ left_distrib := 𝔽₄.mul_add,
  right_distrib := 𝔽₄.add_mul,
  .. 𝔽₄.add_comm_group,
  .. 𝔽₄.comm_monoid }





section cast'

def cast' {R : Type*} [add_group_with_one R] (r : R) : 𝔽₄ → R
| O := 0
| I := 1
| X := r
| Y := r + 1



section ring

variables {R : Type*} [ring R] (h : (2 : R) = 0)
include h

private lemma add_self_eq_zero' (r : R) : r + r = 0 :=
  (two_mul r).symm.trans (mul_eq_zero_of_left h r)

lemma cast'_add (r : R) : ∀ x y : 𝔽₄, cast' r (x + y) = cast' r x + cast' r y
| O x := (zero_add _).symm
| x O := (congr_arg (cast' r) x.add_zero).trans (add_zero _).symm
| I I := h.symm
| I X := add_comm r 1
| I Y := (self_eq_add_right.mpr h).trans (add_left_comm r 1 1)
| X I := rfl
| X X := (add_self_eq_zero' h r).symm
| X Y := (self_eq_add_left.mpr $ add_self_eq_zero' h r).trans (add_assoc r r 1)
| Y I := (self_eq_add_right.mpr h).trans (add_assoc r 1 1).symm
| Y X := (self_eq_add_left.mpr $ add_self_eq_zero' h r).trans (add_right_comm r r 1)
| Y Y := (add_self_eq_zero' h $ r + 1).symm

variables {r : R} (h0 : r * r + r = 1)
include h0

lemma cast'_mul : ∀ x y : 𝔽₄, cast' r (x * y) = cast' r x * cast' r y
| O x := (zero_mul _).symm
| I x := (one_mul _).symm
| x I := (congr_arg (cast' r) x.mul_one).trans (mul_one _).symm
| X O := (mul_zero r).symm
| X X := (add_left_inj r).mp $ (add_right_comm r 1 r).trans $
    (self_eq_add_left.mpr $ add_self_eq_zero' h r).symm.trans h0.symm
| X Y := h0.symm.trans (mul_add_one r r).symm
| Y O := (mul_zero $ r + 1).symm
| Y X := h0.symm.trans (add_one_mul r r).symm
| Y Y := (self_eq_add_right.mpr h).trans $ (add_left_comm r 1 1).trans $
    (congr_arg (+ (r + 1)) ((add_one_mul r r).trans h0).symm).trans (mul_add_one _ r).symm

def cast'_hom : 𝔽₄ →+* R :=
  ⟨cast' r, rfl, cast'_mul h h0, rfl, cast'_add h r⟩

variables (h1 : (1 : R) ≠ 0)
include h1

lemma cast_hom_eq_zero_imp : ∀ x : 𝔽₄, cast'_hom h h0 x = 0 → x = 0
| O := λ _, rfl
| I := λ h2, absurd h2 h1
| X := λ h2, absurd (h0.symm.trans $ (mul_add_one r r).symm.trans $
    mul_eq_zero_of_left h2 $ r + 1) h1
| Y := λ h2, absurd (h0.symm.trans $ (mul_add_one r r).symm.trans $
    mul_eq_zero_of_right r h2) h1

lemma cast_hom_injective : function.injective (cast'_hom h h0) :=
  (injective_iff_map_eq_zero $ cast'_hom h h0).mpr (cast_hom_eq_zero_imp h h0 h1)

end ring

end cast'

end 𝔽₄

end IMO2012A5
end IMOSL
