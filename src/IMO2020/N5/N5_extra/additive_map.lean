import algebra.module.basic

/-!
# Additive maps

Given a commutative additive monoid `M`, we define an additive map `f : ℕ → M` as
  a map such that `f(0) = 0` and `f(xy) = f(x) + f(y)` for all `x, y > 0`.
The set of additive maps form an additive monoid under pointwise addition.
If $M$ has more structures, e.g. `M` is a group or a module,
  then the set of additive maps also has more structures.

## Implementation details

We mimic the implementation from some files in `mathlib` such as `nat.arithmetic_function`.

TODO: Implement module instances for `additive_map M` when `M` is a module over some semiring.
-/

namespace IMOSL
namespace IMO2020N5

structure additive_map (M : Type*) [has_zero M] [has_add M] :=
  (to_fun : ℕ → M) (map_zero' : to_fun 0 = 0)
  (map_mul_add' : ∀ x y : ℕ, 0 < x → 0 < y → to_fun (x * y) = to_fun x + to_fun y)



namespace additive_map

section add_comm_monoid

variables {M : Type*} [add_comm_monoid M]

instance : has_coe_to_fun (additive_map M) (λ _, ℕ → M) := ⟨additive_map.to_fun⟩

@[simp] theorem to_fun_eq_coe (f : additive_map M) : f.to_fun = f := rfl

@[simp] theorem map_zero (f : additive_map M) : f 0 = 0 := f.map_zero'

@[simp] theorem map_mul_add (f : additive_map M) {x y : ℕ} (hx : 0 < x) (hy : 0 < y) :
  f (x * y) = f x + f y := f.map_mul_add' x y hx hy

instance fun_like {M : out_param Type*} [add_comm_monoid M] :
  fun_like (additive_map M) ℕ (λ _, M) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr' }

theorem coe_inj {f g : additive_map M} : (f : ℕ → M) = g ↔ f = g :=
⟨(λ h, fun_like.coe_injective h), (λ h, by rw h)⟩

@[ext] theorem ext {f g : additive_map M} (h : ∀ x, f x = g x) : f = g := fun_like.ext _ _ h

theorem ext_iff {f g : additive_map M} : f = g ↔ ∀ x, f x = g x := ⟨λ h x, by rw h, ext⟩

instance : has_zero (additive_map M) := ⟨⟨(λ _, 0), rfl, (λ _ _ _ _, by rw add_zero)⟩⟩

@[simp] theorem zero_apply {x : ℕ} : (0 : additive_map M) x = 0 := rfl

instance : has_add (additive_map M) :=
⟨λ f g, ⟨(λ n, f n + g n), by rw [map_zero, map_zero, add_zero],
  (λ x y hx hy, by rw [map_mul_add f hx hy, map_mul_add g hx hy, add_add_add_comm])⟩⟩

@[simp] theorem add_apply {f g : additive_map M} {n : ℕ} : (f + g) n = f n + g n := rfl

instance : add_comm_monoid (additive_map M) :=
{ add_comm := λ f g, by ext; simp only [add_apply, add_comm],
  add_assoc := λ f g h, by ext; simp only [add_apply, add_assoc],
  zero_add := λ f, by ext; rw [add_apply, zero_apply, zero_add],
  add_zero := λ f, by ext; rw [add_apply, zero_apply, add_zero],
  .. additive_map.has_zero, .. additive_map.has_add }

end add_comm_monoid



section add_cancel_comm_monoid

variables {M : Type*} [add_cancel_comm_monoid M]

@[simp] theorem map_one_zero (f : additive_map M) : f 1 = 0 :=
  by rw [← add_right_inj (f 1), ← map_mul_add f one_pos one_pos, mul_one, add_zero]

end add_cancel_comm_monoid



section add_comm_group

variables {G : Type*} [add_comm_group G]

instance : has_neg (additive_map G) := ⟨λ f, ⟨(λ n, -(f n)),
  by rw [map_zero, neg_zero], (λ x y hx hy, by rw [map_mul_add f hx hy, neg_add])⟩⟩

@[simp] theorem neg_apply {f : additive_map G} {n : ℕ} : (-f) n = -(f n) := rfl

instance : has_sub (additive_map G) := ⟨λ f g, ⟨(λ n, f n - g n), by simp only [map_zero, sub_zero],
  (λ x y hx hy, by rw [map_mul_add f hx hy, map_mul_add g hx hy, add_sub_add_comm])⟩⟩

@[simp] theorem sub_apply {f g : additive_map G} {n : ℕ} : (f - g) n = f n - g n := rfl

instance : add_comm_group (additive_map G) :=
{ add_left_neg := λ f, by ext; rw [add_apply, neg_apply, neg_add_self, zero_apply],
  .. additive_map.add_comm_monoid, .. additive_map.has_neg }

end add_comm_group

end additive_map

end IMO2020N5
end IMOSL
