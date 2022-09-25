import algebra.module.basic

/-!
# Additive maps

Given a commutative additive monoid `M`, we define an additive map `f : ℕ → M` as
  a map such that `f(0) = f(1) = 0` and `f(xy) = f(x) + f(y)` for all `x y : ℕ` non-zero.
The set of additive maps form an additive monoid under pointwise addition.

## Implementation details

We mimic the implementation from some files in `mathlib` such as `nat.arithmetic_function`.
-/

namespace IMOSL
namespace IMO2020N5

structure additive_map (M : Type*) [has_zero M] [has_add M] :=
  (to_fun : ℕ → M) (map_zero' : to_fun 0 = 0) (map_one' : to_fun 1 = 0)
  (map_mul' : ∀ {x y : ℕ}, x ≠ 0 → y ≠ 0 → to_fun (x * y) = to_fun x + to_fun y)







namespace additive_map

section basic

variables {M : Type*} [has_zero M] [has_add M]

instance : has_coe_to_fun (additive_map M) (λ _, ℕ → M) := ⟨additive_map.to_fun⟩

@[simp] theorem to_fun_eq_coe (f : additive_map M) : f.to_fun = f := rfl

@[simp] theorem map_zero (f : additive_map M) : f 0 = 0 := f.map_zero'

@[simp] theorem map_one (f : additive_map M) : f 1 = 0 := f.map_one'

@[simp] theorem map_mul (f : additive_map M) {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
  f (x * y) = f x + f y := f.map_mul' hx hy

instance fun_like {M : out_param Type*} [has_zero M] [has_add M] :
  fun_like (additive_map M) ℕ (λ _, M) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

theorem coe_inj {f g : additive_map M} : (f : ℕ → M) = g ↔ f = g :=
⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : additive_map M} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

theorem ext_iff {f g : additive_map M} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

end basic



section add_comm_monoid

variables {M : Type*} [add_comm_monoid M]

instance : has_zero (additive_map M) := ⟨⟨(λ _, 0), rfl, rfl, (λ _ _ _ _, by rw add_zero)⟩⟩

@[simp] theorem zero_apply {x : ℕ} : (0 : additive_map M) x = 0 := rfl

instance : has_add (additive_map M) :=
⟨λ f g, ⟨(λ n, f n + g n),
  by rw [map_zero, map_zero, add_zero],
  by rw [map_one, map_one, add_zero],
  λ x y hx hy, by rw [map_mul f hx hy, map_mul g hx hy, add_add_add_comm]⟩⟩

@[simp] theorem add_apply {f g : additive_map M} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_comm_monoid (additive_map M) :=
{ add_comm := λ f g, by ext; simp only [add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply, add_assoc],
  zero_add := λ f, by ext; rw [add_apply, zero_apply, zero_add],
  add_zero := λ f, by ext; rw [add_apply, zero_apply, add_zero],
  .. additive_map.has_zero, .. additive_map.has_add }

@[simp] theorem map_pow (f : additive_map M) (x n : ℕ) :
  f (x ^ n) = n • f x :=
begin
  induction n with n n_ih,
  rw [pow_zero, zero_smul, map_one],
  by_cases hx : x = 0,
  rw [hx, pow_succ, zero_mul, map_zero, smul_zero],
  rw [pow_succ', map_mul f (pow_ne_zero _ hx) hx, nat.succ_eq_add_one, n_ih, add_smul, one_smul]
end

end add_comm_monoid



section mul_action

variables {M : Type*} [add_comm_monoid M] {α : Type*} [monoid α] [distrib_mul_action α M]

instance : has_smul α (additive_map M) :=
⟨λ a f, ⟨λ x, a • f x,
  by rw [map_zero, smul_zero],
  by rw [map_one, smul_zero],
  λ x y hx hy, by rw [map_mul f hx hy, smul_add]⟩⟩

@[simp] theorem smul_def {a : α} {f : additive_map M} {x : ℕ} : (a • f) x = a • f x := rfl

instance : mul_action α (additive_map M) :=
{ one_smul := λ f, by ext; rw [smul_def, one_smul],
  mul_smul := λ x y f, by ext; simp only [smul_def]; rw mul_smul }

instance : distrib_mul_action α (additive_map M) :=
{ smul_add := λ x f g, by ext; simp only [smul_def, add_apply]; rw smul_add,
  smul_zero := λ x, by ext; rw [smul_def, zero_apply, smul_zero] }

end mul_action



section add_comm_group

variables {G : Type*} [add_comm_group G]

instance : has_neg (additive_map G) :=
⟨λ f, ⟨(λ n, -(f n)),
  by rw [map_zero, neg_zero],
  by rw [map_one, neg_zero],
  λ x y hx hy, by rw [map_mul f hx hy, neg_add]⟩⟩

@[simp] theorem neg_apply {f : additive_map G} {n : ℕ} : (-f) n = -(f n) := rfl

instance : has_sub (additive_map G) :=
⟨λ f g, ⟨(λ n, f n - g n),
  by simp only [map_zero, sub_zero],
  by simp only [map_one, sub_zero],
  λ x y hx hy, by rw [map_mul f hx hy, map_mul g hx hy, add_sub_add_comm]⟩⟩

@[simp] theorem sub_apply {f g : additive_map G} {n : ℕ} : (f - g) n = f n - g n := rfl

instance : add_comm_group (additive_map G) :=
{ add_left_neg := λ f, by ext; rw [add_apply, neg_apply, neg_add_self, zero_apply],
  .. additive_map.add_comm_monoid, .. additive_map.has_neg }

end add_comm_group

end additive_map

end IMO2020N5
end IMOSL
