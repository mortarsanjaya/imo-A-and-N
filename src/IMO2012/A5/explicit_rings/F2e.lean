import algebra.hom.ring

/-!
# Explicit construction of 𝔽₂[X]/⟨X²⟩

In this file, we explicitly construct the ring `𝔽₂[ε] := 𝔽₂[X]/⟨X²⟩`.
We prove just the necessary properties for the purpose of the main problem.
The explicit construction is used instead of the `dual_number` API for
  the purpose of avoiding the use of `algebra` instances.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₂ε
| O : 𝔽₂ε
| I : 𝔽₂ε
| X : 𝔽₂ε
| Y : 𝔽₂ε





namespace 𝔽₂ε

protected def repr : 𝔽₂ε → string
| O := "0"
| I := "1"
| X := "ε"
| Y := "ε + 1"

instance : has_repr 𝔽₂ε := ⟨𝔽₂ε.repr⟩



protected def add : 𝔽₂ε → 𝔽₂ε → 𝔽₂ε
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

protected def mul : 𝔽₂ε → 𝔽₂ε → 𝔽₂ε
| O x := O
| I x := x
| X O := O
| X I := X
| X X := O
| X Y := X
| Y O := O
| Y I := Y
| Y X := X
| Y Y := I

instance : has_zero 𝔽₂ε := ⟨O⟩
instance : has_one 𝔽₂ε := ⟨I⟩
instance : has_add 𝔽₂ε := ⟨𝔽₂ε.add⟩
instance : has_neg 𝔽₂ε := ⟨id⟩
instance : has_mul 𝔽₂ε := ⟨𝔽₂ε.mul⟩



protected lemma add_zero : ∀ x : 𝔽₂ε, x + 0 = x
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

protected lemma zero_add (x : 𝔽₂ε) : 0 + x = x := rfl

protected lemma add_comm : ∀ x y : 𝔽₂ε, x + y = y + x
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

protected lemma add_assoc : ∀ x y z : 𝔽₂ε, x + y + z = x + (y + z)
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

protected lemma add_left_neg : ∀ x : 𝔽₂ε, -x + x = 0
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

instance : add_comm_group 𝔽₂ε :=
{ add_comm := 𝔽₂ε.add_comm,
  add_assoc := 𝔽₂ε.add_assoc,
  add_zero := 𝔽₂ε.add_zero,
  zero_add := 𝔽₂ε.zero_add,
  add_left_neg := 𝔽₂ε.add_left_neg,
  .. 𝔽₂ε.has_add,
  .. 𝔽₂ε.has_zero,
  .. 𝔽₂ε.has_neg }



protected lemma mul_one : ∀ x : 𝔽₂ε, x * 1 = x
| O := rfl
| I := rfl
| X := rfl
| Y := rfl

protected lemma one_mul (x : 𝔽₂ε) : 1 * x = x := rfl

protected lemma mul_comm : ∀ x y : 𝔽₂ε, x * y = y * x
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

protected lemma mul_assoc : ∀ x y z : 𝔽₂ε, x * y * z = x * (y * z)
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

instance : comm_monoid 𝔽₂ε :=
{ mul_comm := 𝔽₂ε.mul_comm,
  mul_assoc := 𝔽₂ε.mul_assoc,
  one_mul := 𝔽₂ε.one_mul,
  mul_one := 𝔽₂ε.mul_one,
  .. 𝔽₂ε.has_mul,
  .. 𝔽₂ε.has_one }



protected lemma mul_add : ∀ x y z : 𝔽₂ε, x * (y + z) = x * y + x * z
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

protected lemma add_mul (x y z : 𝔽₂ε) : (x + y) * z = x * z + y * z :=
  (𝔽₂ε.mul_comm _ z).trans $ (𝔽₂ε.mul_add z x y).trans $
    congr_arg2 𝔽₂ε.add (𝔽₂ε.mul_comm z x) (𝔽₂ε.mul_comm z y)

instance : comm_ring 𝔽₂ε :=
{ left_distrib := 𝔽₂ε.mul_add,
  right_distrib := 𝔽₂ε.add_mul,
  .. 𝔽₂ε.add_comm_group,
  .. 𝔽₂ε.comm_monoid }





section cast'

def cast' {R : Type*} [add_group_with_one R] (r : R) : 𝔽₂ε → R
| O := 0
| I := 1
| X := r
| Y := r + 1



section ring

variables {R : Type*} [ring R] (h : (2 : R) = 0)
include h

private lemma add_self_eq_zero' (r : R) : r + r = 0 :=
  (two_mul r).symm.trans (mul_eq_zero_of_left h r)

lemma cast'_add (r : R) : ∀ x y : 𝔽₂ε, cast' r (x + y) = cast' r x + cast' r y
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

variables {r : R} (h0 : r * r = 0)
include h0

lemma cast'_mul : ∀ x y : 𝔽₂ε, cast' r (x * y) = cast' r x * cast' r y
| O x := (zero_mul _).symm
| I x := (one_mul _).symm
| x I := (congr_arg (cast' r) x.mul_one).trans (mul_one _).symm
| X O := (mul_zero r).symm
| X X := h0.symm
| X Y := (add_left_eq_self.mpr h0).symm.trans (mul_add_one r r).symm
| Y O := (mul_zero $ r + 1).symm
| Y X := (add_left_eq_self.mpr h0).symm.trans (add_one_mul r r).symm
| Y Y := eq.symm $ (mul_add_one (r + 1) r).trans $ (add_assoc _ _ _).symm.trans $
    add_left_eq_self.mpr $ by rwa [← add_one_mul, add_assoc, ← bit0, h, add_zero]

def cast'_hom : 𝔽₂ε →+* R :=
  ⟨cast' r, rfl, cast'_mul h h0, rfl, cast'_add h r⟩

variables (h1 : (r : R) ≠ 0)
include h1

lemma cast'_hom_eq_zero_imp : ∀ x : 𝔽₂ε, cast'_hom h h0 x = 0 → x = 0
| O := λ _, rfl
| I := λ h2, absurd ((one_mul r).symm.trans $ (congr_arg (* r) h2).trans (zero_mul r)) h1
| X := λ h2, absurd h2 h1
| Y := λ h2, let h3 := eq_neg_of_add_eq_zero_left h2 in
    absurd h0 $ by rwa [h3, mul_neg_one, neg_eq_zero, ← h3]

lemma cast'_hom_injective : function.injective (cast'_hom h h0) :=
  (injective_iff_map_eq_zero $ cast'_hom h h0).mpr (cast'_hom_eq_zero_imp h h0 h1)

end ring

end cast'

end 𝔽₂ε

end IMO2012A5
end IMOSL
