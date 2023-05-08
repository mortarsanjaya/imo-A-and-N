import algebra.char_p.basic

/-!
# Explicit construction of 𝔽₃

In this file, we explicitly construct the field of 3 elements.
Every ring with 3 elements is isomorphic to `𝔽₃`; we will also define the isomorphism.
The implementation for this isomorphism is mostly copied from `data.zmod.basic`.
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
instance : has_div 𝔽₃ := ⟨𝔽₃.mul⟩
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

instance : fintype 𝔽₃ :=
{ elems := {𝔽₃0, 𝔽₃1, 𝔽₃2},
  complete := λ x, match x with
    | 𝔽₃0 := finset.mem_insert_self 𝔽₃0 {𝔽₃1, 𝔽₃2}
    | 𝔽₃1 := finset.mem_insert_of_mem $ finset.mem_insert_self 𝔽₃1 {𝔽₃2}
    | 𝔽₃2 := finset.mem_insert_of_mem $ finset.mem_insert_of_mem $
               finset.mem_singleton_self 𝔽₃2
  end }

protected lemma card_eq : fintype.card 𝔽₃ = 3 := rfl

instance : nontrivial 𝔽₃ :=
{ exists_pair_ne := ⟨𝔽₃0, 𝔽₃1, λ h, 𝔽₃.no_confusion h⟩ }



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

protected lemma mul_zero : ∀ x : 𝔽₃, x * 0 = 0
| 𝔽₃0 := rfl
| 𝔽₃1 := rfl
| 𝔽₃2 := rfl

protected lemma zero_mul (x : 𝔽₃) : 0 * x = 0 :=
  (𝔽₃.mul_comm 0 x).trans (𝔽₃.mul_zero x)

protected lemma mul_inv_cancel : ∀ x : 𝔽₃, x ≠ 0 → x * x⁻¹ = 1
| 𝔽₃0 := absurd rfl
| 𝔽₃1 := λ _, rfl
| 𝔽₃2 := λ _, rfl

instance : comm_group_with_zero 𝔽₃ :=
{ mul_comm := 𝔽₃.mul_comm,
  mul_assoc := 𝔽₃.mul_assoc,
  one_mul := 𝔽₃.one_mul,
  mul_one := 𝔽₃.mul_one,
  mul_zero := 𝔽₃.mul_zero,
  zero_mul := 𝔽₃.zero_mul,
  inv_zero := rfl,
  mul_inv_cancel := 𝔽₃.mul_inv_cancel,
  .. 𝔽₃.has_zero,
  .. 𝔽₃.has_mul,
  .. 𝔽₃.has_one,
  .. 𝔽₃.has_inv,
  .. 𝔽₃.nontrivial }



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

instance : field 𝔽₃ :=
{ left_distrib := 𝔽₃.mul_add,
  right_distrib := 𝔽₃.add_mul,
  .. 𝔽₃.add_comm_group,
  .. 𝔽₃.comm_group_with_zero }



lemma three_eq_zero : (3 : 𝔽₃) = 0 := rfl

lemma ring_char_eq_three : ring_char 𝔽₃ = 3 :=
  char_p.ring_char_of_prime_eq_zero nat.prime_three three_eq_zero

instance char_p : char_p 𝔽₃ 3 :=
  ring_char.of_eq ring_char_eq_three





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
| 𝔽₃0 𝔽₃0 := (zero_add 0).symm
| 𝔽₃0 𝔽₃1 := (zero_add 1).symm
| 𝔽₃0 𝔽₃2 := (zero_add (-1)).symm
| 𝔽₃1 𝔽₃0 := (add_zero 1).symm
| 𝔽₃1 𝔽₃1 := eq.symm (eq_neg_of_add_eq_zero_left h)
| 𝔽₃1 𝔽₃2 := (add_neg_self 1).symm
| 𝔽₃2 𝔽₃0 := (add_zero (-1)).symm
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


section ring_equiv

variables {R : Type*} [ring R] [fintype R] (h : fintype.card R = 3)
include h

lemma three_eq_zero_of_card : (3 : R) = 0 :=
  by rw [← char_p.cast_card_eq_zero R, h, nat.cast_bit1, nat.cast_one]

lemma one_ne_zero_of_card : (1 : R) ≠ 0 :=
  by haveI : nontrivial R := fintype.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_eq (nat.succ_lt_succ $ nat.succ_pos 1) h.symm);
  exact (ne_zero.one R).out

lemma cast_hom_bijective : function.bijective (cast_hom $ three_eq_zero_of_card h) :=
  (fintype.bijective_iff_injective_and_card _).mpr
    ⟨cast_hom_injective _ (one_ne_zero_of_card h), 𝔽₃.card_eq.trans h.symm⟩

noncomputable def ring_equiv : 𝔽₃ ≃+* R :=
  ring_equiv.of_bijective _ (cast_hom_bijective h)

end ring_equiv

end cast

end 𝔽₃

end IMO2012A5
end IMOSL
