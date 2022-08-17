import IMO2020.N5.N5_extra.good_map

/-!
# `p`-strong additive maps

We construct the type of `p`-strong additive maps here.
The characterization of `p`-strong additive maps will be done in `characterization.lean`.

## Implementation details

A huge part of code written for this file is taken from `mathlib`'s abstract algebra files.
This is similar to the file `additive_map.lean`.
-/

namespace IMOSL
namespace IMO2020N5

open additive_map
open_locale classical

@[ancestor additive_map]
structure strong_map (M : Type*) [has_zero M] [has_add M] (p : ℕ) extends additive_map M :=
(is_strong' : strong p to_fun)



namespace strong_map

section add_comm_monoid

variables {M : Type*} [add_comm_monoid M] {p : ℕ}

instance : has_coe_to_fun (strong_map M p) (λ (f : strong_map M p), ℕ → M) :=
⟨λ f, (strong_map.to_additive_map f).to_fun⟩

@[simp] theorem to_fun_eq_coe (f : strong_map M p) : f.to_fun = f := rfl

@[simp] theorem map_zero (f : strong_map M p) : f 0 = 0 := f.map_zero'

theorem map_mul_add (f : strong_map M p) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
  f (x * y) = f x + f y := f.map_mul_add' hx hy

theorem is_strong (f : strong_map M p) : strong p f := f.is_strong'

instance fun_like {M : out_param Type*} [add_comm_monoid M] {p : ℕ} :
  fun_like (strong_map M p) ℕ (λ _, M) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; simp at h; congr' }

instance has_coe_additive_map : has_coe (strong_map M p) (additive_map M) :=
  ⟨strong_map.to_additive_map⟩

@[simp, norm_cast] lemma coe_additive_map (f : strong_map M p) : ⇑(f : additive_map M) = f := rfl

theorem coe_inj {f g : strong_map M p} : (f : ℕ → M) = g ↔ f = g :=
  ⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : strong_map M p} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

theorem ext_iff {f g : strong_map M p} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

instance : has_zero (strong_map M p) := ⟨⟨0, λ _ _ _ _ _ _, by simp⟩⟩

@[simp] theorem zero_apply {x : ℕ} : (0 : strong_map M p) x = 0 := rfl

instance : has_add (strong_map M p) := ⟨λ f g, ⟨f + g, λ k a b ha hb h,
    by simp; rw [is_strong f k a b ha hb h, is_strong g k a b ha hb h]⟩⟩

@[simp] theorem add_apply {f g : strong_map M p} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_comm_monoid (strong_map M p) :=
{ add_comm := λ f g, by ext; simp only [add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply, add_assoc],
  zero_add := λ f, by ext; rw [add_apply, zero_apply, zero_add],
  add_zero := λ f, by ext; rw [add_apply, zero_apply, add_zero],
  .. strong_map.has_zero, .. strong_map.has_add }

end add_comm_monoid



section mul_action

variables {M : Type*} [add_comm_monoid M] {p : ℕ} {α : Type*} [monoid α] [distrib_mul_action α M]

instance : has_smul α (strong_map M p) :=
  ⟨λ x f, ⟨x • f, λ k a b ha hb h, by simp; rw is_strong f k a b ha hb h⟩⟩

@[simp] theorem smul_def {a : α} {f : strong_map M p} {x : ℕ} : (a • f) x = a • f x := rfl

instance : mul_action α (strong_map M p) :=
{ one_smul := λ f, by ext; rw [smul_def, one_smul],
  mul_smul := λ x y f, by ext; simp only [smul_def]; rw mul_smul }

instance : distrib_mul_action α (strong_map M p) :=
{ smul_add := λ x f g, by ext; simp only [smul_def, add_apply]; rw smul_add,
  smul_zero := λ x, by ext; rw [smul_def, zero_apply, smul_zero] }

end mul_action



section add_cancel_comm_monoid

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ}

@[simp] theorem map_one_zero (f : strong_map M p) : f 1 = 0 :=
  additive_map.map_one_zero f

@[simp] theorem map_pow_smul (f : strong_map M p) {x : ℕ} (hx : x ≠ 0) (n : ℕ) :
  f (x ^ n) = n • f x := additive_map.map_pow_smul f hx n

end add_cancel_comm_monoid



section add_comm_group

variables {G : Type*} [add_comm_group G] {p : ℕ}

instance : has_neg (strong_map G p) := ⟨λ f, ⟨-(f : additive_map G),
  λ k a b ha hb h, by simp; exact is_strong f k a b ha hb h⟩⟩

@[simp] theorem neg_apply {f : strong_map G p} {n : ℕ} : (-f) n = -(f n) := rfl

instance : has_sub (strong_map G p) := ⟨λ f g, ⟨(f : additive_map G) - g,
  λ k a b ha hb h, by simp; rw [is_strong f k a b ha hb h, is_strong g k a b ha hb h]⟩⟩

@[simp] theorem sub_apply {f g : strong_map G p} {n : ℕ} : (f - g) n = f n - g n := rfl

instance : add_comm_group (strong_map G p) :=
{ add_left_neg := λ f, by ext; rw [add_apply, neg_apply, neg_add_self, zero_apply],
  .. strong_map.add_comm_monoid, .. strong_map.has_neg }

end add_comm_group

end strong_map

end IMO2020N5
end IMOSL
