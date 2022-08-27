import data.zmod.basic

/-!
# `p`-complement homomorphism

In the context of strong maps, a `p`-complementary homomorphism is the
  set of maps `χ : additive (zmod p)ˣ →+ M` such that `χ(-1) = 0`.
The structure is denoted by `pcompl_hom M p`.
It is an important part in the classification of `p`-strong maps.
-/

namespace IMOSL
namespace IMO2020N5

/-- The type of maps `χ : additive (zmod p)ˣ →+ M` for which `χ(-1) = 0` -/
structure pcompl_hom (M : Type*) [add_comm_monoid M] (p : ℕ) extends additive (zmod p)ˣ →+ M :=
  (map_neg_one' : to_fun (additive.of_mul (-1)) = 0)



namespace pcompl_hom

section add_comm_monoid

variables {M : Type*} [add_comm_monoid M] {p : ℕ}

/-- Instead of coercing to `additive (zmod p)ˣ → M`,
  we coerce to `(zmod p)ˣ → M` for an *unknown* reason. -/
instance : has_coe_to_fun (pcompl_hom M p) (λ (_ : pcompl_hom M p), (zmod p)ˣ → M) :=
  ⟨λ f, (pcompl_hom.to_add_monoid_hom f).to_fun⟩

@[simp] theorem to_fun_eq_coe (f : pcompl_hom M p) : f.to_fun = f := rfl

@[simp] theorem map_one (f : pcompl_hom M p) : f 1 = 0 := f.map_zero'

@[simp] theorem map_mul_add (f : pcompl_hom M p) {x y : (zmod p)ˣ} : f (x * y) = f x + f y :=
  f.map_add' x y

@[simp] theorem map_neg_one (f : pcompl_hom M p) : f (-1) = 0 := f.map_neg_one'

@[simp] theorem map_additive (f : pcompl_hom M p) {x : (zmod p)ˣ} :
  f (additive.of_mul x) = f x := rfl

instance fun_like {M : out_param Type*} [add_comm_monoid M] {p : ℕ} :
  fun_like (pcompl_hom M p) (zmod p)ˣ (λ _, M) :=
  ⟨(λ f, f.to_fun), (λ f g h, by cases f; cases g; simp at h; congr')⟩

instance has_coe_add_monoid_hom : has_coe (pcompl_hom M p) (additive (zmod p)ˣ →+ M) :=
  ⟨pcompl_hom.to_add_monoid_hom⟩

@[simp, norm_cast] lemma coe_add_monoid_hom (f : pcompl_hom M p) :
  ⇑(f : additive (zmod p)ˣ →+ M) = f := rfl

theorem coe_inj {f g : pcompl_hom M p} : (f : additive (zmod p)ˣ → M) = g ↔ f = g :=
  ⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : pcompl_hom M p} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

theorem ext_iff {f g : pcompl_hom M p} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

instance : has_zero (pcompl_hom M p) :=
  ⟨⟨0, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.zero_apply]⟩⟩

@[simp] theorem zero_apply {x : (zmod p)ˣ} : (0 : pcompl_hom M p) x = 0 := rfl

instance : has_add (pcompl_hom M p) :=
  ⟨λ f g, ⟨f + g, by rw [add_monoid_hom.to_fun_eq_coe, add_monoid_hom.add_apply];
    simp only [coe_add_monoid_hom, map_additive, map_neg_one, add_zero]⟩⟩

@[simp] theorem add_apply {f g : pcompl_hom M p} {x : (zmod p)ˣ} : (f + g) x = f x + g x := rfl

instance : add_comm_monoid (pcompl_hom M p) :=
{ add_comm := λ f g, by ext; rw [add_apply, add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply]; rw add_assoc,
  zero_add := λ f, by ext; rw [add_apply, zero_apply, zero_add],
  add_zero := λ f, by ext; rw [add_apply, zero_apply, add_zero],
  .. pcompl_hom.has_zero, .. pcompl_hom.has_add }

@[simp] theorem nsmul_apply (n : ℕ) (f : pcompl_hom M p) (x : (zmod p)ˣ) : (n • f) x = n • f x :=
begin
  induction n with n n_ih,
  rw [zero_smul, zero_smul, zero_apply],
  rw [nat.succ_eq_add_one, add_smul, one_smul, add_smul, one_smul, add_apply, n_ih]
end

end add_comm_monoid



section add_cancel_comm_monoid

variables {M : Type*} [add_cancel_comm_monoid M] {p : ℕ}

@[simp] theorem map_pow_smul (f : pcompl_hom M p) {x : (zmod p)ˣ} {n : ℕ} : f (x ^ n) = n • f x :=
begin
  induction n with n n_ih,
  rw [pow_zero, zero_smul, map_one],
  rw [pow_succ', map_mul_add, n_ih, nat.succ_eq_add_one, add_smul, one_smul]
end

end add_cancel_comm_monoid


end pcompl_hom

end IMO2020N5
end IMOSL
