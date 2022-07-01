import algebra.char_p.two algebra.char_p.pi

/-!
## Alternative formulation of IMO 2017 A6 for the case char(F) = 2

Let F be a field of characteristic 2.
Find all functions f : F → F such that:
1. ∀ x y ∈ F, f(f(x) f(y)) + f(x + y) = f(xy + x + y)
2. ∀ x ∈ F, f(x + 1) = f(x) + 1
-/

open char_two
open_locale classical

namespace IMOSL
namespace IMO2017A6alt

variables {F : Type*} [field F] [char_p F 2]

def fn_eq1 (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y + x + y)
def fn_eq2 (f : F → F) := ∀ x : F, f (x + 1) = f x + 1



namespace base

variables {f : F → F} (feq1 : fn_eq1 f) (feq2 : fn_eq2 f)
include feq1 feq2



lemma lem1 : f 0 = 0 :=
begin
  have h := feq1 0 0,
  rw [mul_zero, add_zero, add_zero, add_left_eq_self] at h,
  have h0 := feq1 (f 0 * f 0) 0,
  rwa [h, zero_mul, mul_zero, zero_add, add_zero, add_left_eq_self] at h0
end

lemma lem2 : f 1 = 1 :=
  by rw [← zero_add (1 : F), feq2, lem1 feq1 feq2]

lemma lem3 (x : F) : f x = 0 ↔ x = 0 :=
begin
  rw iff.comm; split,
  rintros rfl; exact lem1 feq1 feq2,
  intros h; by_contra h0,
  have h1 := feq1 x x⁻¹,
  rw [h, zero_mul, lem1 feq1 feq2, zero_add, mul_inv_cancel h0,
      add_assoc, add_comm (1 : F), feq2, eq_comm, add_right_eq_self] at h1,
  exact one_ne_zero h1
end



---- More results specialized for case char(F) = 2
lemma lem4 (x : F) : f (f x) = f x :=
begin
  have h := feq1 x 1,
  rwa [mul_one, char_two.add_self_eq_zero, zero_add, lem2 feq1 feq2,
       mul_one, feq2, ← add_assoc, add_left_eq_self, ← sub_eq_add, sub_eq_zero] at h
end

lemma lem5 (x : F) : f x = 1 ↔ x = 1 :=
  by rw [← sub_eq_zero, sub_eq_add, ← feq2, lem3 feq1 feq2, ← sub_eq_add, sub_eq_zero]

lemma lem6 (x : F) : f (x⁻¹) = (f x)⁻¹ :=
begin
  by_cases h : x = 0,
  rw [h, inv_zero, lem1 feq1 feq2, inv_zero],
  have h0 := feq1 x x⁻¹,
  rw [mul_inv_cancel h, add_assoc, (add_comm (1 : F)), feq2,
      add_comm, add_right_inj, lem5 feq1 feq2] at h0,
  rw inv_eq_of_mul_eq_one_right h0
end

lemma lem7 (x y : F) : f (f x * f y) + f (x + y) + 1 = f ((x + 1) * (y + 1)) :=
  by rw [feq1, ← feq2, ← mul_add_one, add_assoc, ← add_one_mul]

lemma lem8 (x y : F) : f ((f x + 1) * (f y + 1)) + 1 = f (x * y) + f (x + y) :=
begin
  have h := lem7 feq1 feq2 (x + 1) (y + 1),
  rw [feq2, feq2, add_right_comm, ← eq_sub_iff_add_eq] at h,
  rw [h, sub_eq_add, add_assoc, add_assoc, add_add_add_comm,
      char_two.add_self_eq_zero, add_zero, add_zero, add_zero],
end

lemma lem9 {a b : F} (h : f a = f b) (x : F) : f (a * x) + f (a + x) = f(b * x) + f (b + x) :=
  by rw [← lem8 feq1 feq2, h, lem8 feq1 feq2]

lemma lem10 {a b c d : F} (h : f a = f b) (h0 : f c = f d) :
  f (a * c) + f (a + c) = f(b * d) + f (b + d) :=
  by rw [lem9 feq1 feq2 h, add_comm b, mul_comm,
         lem9 feq1 feq2 h0, add_comm d, mul_comm]

end base

end IMO2017A6alt
end IMOSL
