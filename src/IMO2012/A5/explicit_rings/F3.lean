import algebra.field.defs data.fintype.basic

/-!
# Explicit construction of 𝔽₃

In this file, we explicitly construct the field of `3` elements.
Every ring with `3` elements is isomorphic to `𝔽₃`; we will also define the isomorphism.
-/

namespace IMOSL
namespace IMO2012A5

inductive 𝔽₃
| 𝔽₃0 : 𝔽₃
| 𝔽₃1 : 𝔽₃
| 𝔽₃2 : 𝔽₃





namespace 𝔽₃

def repr : 𝔽₃ → string
| 𝔽₃0 := "0"
| 𝔽₃1 := "1"
| 𝔽₃2 := "2"

instance : has_repr 𝔽₃ := ⟨repr⟩



def add : 𝔽₃ → 𝔽₃ → 𝔽₃
| 𝔽₃0 x := x
| x 𝔽₃0 := x
| 𝔽₃1 𝔽₃1 := 𝔽₃2
| 𝔽₃1 𝔽₃2 := 𝔽₃0
| 𝔽₃2 𝔽₃1 := 𝔽₃0
| 𝔽₃2 𝔽₃2 := 𝔽₃1

def sub : 𝔽₃ → 𝔽₃ → 𝔽₃
| x 𝔽₃0 := x
| 𝔽₃0 𝔽₃1 := 𝔽₃2
| 𝔽₃0 𝔽₃2 := 𝔽₃1
| 𝔽₃1 𝔽₃1 := 𝔽₃0
| 𝔽₃1 𝔽₃2 := 𝔽₃2
| 𝔽₃2 𝔽₃1 := 𝔽₃1
| 𝔽₃2 𝔽₃2 := 𝔽₃0

def neg : 𝔽₃ → 𝔽₃ 
| 𝔽₃0 := 𝔽₃0
| 𝔽₃1 := 𝔽₃2
| 𝔽₃2 := 𝔽₃1

def mul : 𝔽₃ → 𝔽₃ → 𝔽₃
| 𝔽₃0 x := 𝔽₃0
| 𝔽₃1 x := x
| 𝔽₃2 𝔽₃0 := 𝔽₃0
| 𝔽₃2 𝔽₃1 := 𝔽₃2
| 𝔽₃2 𝔽₃2 := 𝔽₃1

instance : has_zero 𝔽₃ := ⟨𝔽₃0⟩
instance : has_one 𝔽₃ := ⟨𝔽₃1⟩
instance : has_add 𝔽₃ := ⟨add⟩
instance : has_sub 𝔽₃ := ⟨sub⟩
instance : has_neg 𝔽₃ := ⟨neg⟩
instance : has_mul 𝔽₃ := ⟨mul⟩
instance : has_div 𝔽₃ := ⟨mul⟩
instance : has_inv 𝔽₃ := ⟨id⟩

instance : decidable_eq 𝔽₃
| 𝔽₃0 𝔽₃0 := is_true rfl
| 𝔽₃0 𝔽₃1 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃0 𝔽₃2 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃1 𝔽₃0 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃1 𝔽₃1 := is_true rfl
| 𝔽₃1 𝔽₃2 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃2 𝔽₃0 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃2 𝔽₃1 := is_false (λ h, 𝔽₃.no_confusion h)
| 𝔽₃2 𝔽₃2 := is_true rfl

instance : nontrivial 𝔽₃ :=
{ exists_pair_ne := ⟨𝔽₃0, 𝔽₃1, λ h, 𝔽₃.no_confusion h⟩ }

section fintype
open finset
instance : fintype 𝔽₃ :=
{ elems := {𝔽₃0, 𝔽₃1, 𝔽₃2},
  complete := λ x, match x with
    | 𝔽₃0 := mem_insert_self 𝔽₃0 {𝔽₃1, 𝔽₃2}
    | 𝔽₃1 := mem_insert_of_mem $ mem_insert_self 𝔽₃1 {𝔽₃2}
    | 𝔽₃2 := mem_insert_of_mem $ mem_insert_of_mem $ mem_singleton_self 𝔽₃2
  end }
end fintype


lemma add_comm : ∀ x y : 𝔽₃, x + y = y + x
| 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 := rfl

lemma add_assoc : ∀ x y z : 𝔽₃, x + y + z = x + (y + z)
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

lemma add_zero : ∀ x : 𝔽₃, x + 0 = x
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

lemma zero_add (x : 𝔽₃) : 0 + x = x :=
  (add_comm 0 x).trans (add_zero x)

lemma add_left_neg : ∀ x : 𝔽₃, -x + x = 0
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

instance : add_comm_group 𝔽₃ :=
{ add_comm := add_comm,
  add_assoc := add_assoc,
  add_zero := add_zero,
  zero_add := zero_add,
  add_left_neg := add_left_neg,
  .. 𝔽₃.has_add,
  .. 𝔽₃.has_zero,
  .. 𝔽₃.has_neg }



lemma mul_comm : ∀ x y : 𝔽₃, x * y = y * x
| 𝔽₃0 𝔽₃0 := rfl
| 𝔽₃0 𝔽₃1 := rfl
| 𝔽₃0 𝔽₃2 := rfl
| 𝔽₃1 𝔽₃0 := rfl
| 𝔽₃1 𝔽₃1 := rfl
| 𝔽₃1 𝔽₃2 := rfl
| 𝔽₃2 𝔽₃0 := rfl
| 𝔽₃2 𝔽₃1 := rfl
| 𝔽₃2 𝔽₃2 := rfl

lemma mul_assoc : ∀ x y z : 𝔽₃, x * y * z = x * (y * z)
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

lemma mul_one : ∀ x : 𝔽₃, x * 1 = x
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

lemma one_mul (x : 𝔽₃) : 1 * x = x :=
  (mul_comm 1 x).trans (mul_one x)

lemma mul_zero : ∀ x : 𝔽₃, x * 0 = 0
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

lemma zero_mul (x : 𝔽₃) : 0 * x = 0 :=
  (mul_comm 0 x).trans (mul_zero x)

lemma mul_inv_cancel : ∀ x : 𝔽₃, x ≠ 0 → x * x⁻¹ = 1
| 𝔽₃0 := absurd rfl
| 𝔽₃1 := λ _, rfl
| 𝔽₃2 := λ _, rfl

instance : comm_group_with_zero 𝔽₃ :=
{ mul_comm := mul_comm,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_zero := mul_zero,
  zero_mul := zero_mul,
  inv_zero := rfl,
  mul_inv_cancel := mul_inv_cancel,
  .. 𝔽₃.has_zero,
  .. 𝔽₃.has_mul,
  .. 𝔽₃.has_one,
  .. 𝔽₃.has_inv,
  .. 𝔽₃.nontrivial }


lemma mul_add : ∀ x y z : 𝔽₃, x * (y + z) = x * y + x * z
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

lemma add_mul (x y z : 𝔽₃) : (x + y) * z = x * z + y * z :=
  (mul_comm _ z).trans $ (mul_add z x y).trans $
    congr_arg2 has_add.add (mul_comm z x) (mul_comm z y)

instance : field 𝔽₃ :=
{ left_distrib := mul_add,
  right_distrib := add_mul,
  .. 𝔽₃.add_comm_group,
  .. 𝔽₃.comm_group_with_zero }

end 𝔽₃

end IMO2012A5
end IMOSL
