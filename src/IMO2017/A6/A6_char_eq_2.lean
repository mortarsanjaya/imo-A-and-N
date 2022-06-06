import
  IMO2017.A6.A6_general
  algebra.char_p.basic
  algebra.char_p.pi
  algebra.char_p.two
  logic.function.basic

/-
  My progress of 2017 A6 for the case char(F) = 2
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]



namespace case_char_eq_2

open function
open char_two

variable [char_p F 2]







---- Start with new definitions
def fn_eq1 (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y + x + y)
def fn_eq2 (f : F → F) := ∀ x : F, f (x + 1) = f x + 1



---- Correspondence between the new FE and the old FE
---- In particular, we show that solving our FE system is equivalent to solving the old FE
---- (Exclude the case where f = 0)
namespace correspondence

lemma fn_corr_lem1 (f : F → F) :
  fn_eq F f → f ≠ 0 → f 0 = 1 :=
begin
  intros feq h,
  rw [← sub_eq_zero, ← sq_eq_zero_iff, sub_eq_add,
      char_two.add_sq, general.fn_lem3_3 F f feq h],
  simp,
end

lemma fn_corr_lem2 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq2 F f :=
begin
  intros feq h x,
  rw [general.fn_lem4_1 F f feq (fn_corr_lem1 F f feq h), sub_eq_add],
end

theorem fn_corr1 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq1 F (f + 1) :=
begin
  intros feq h x y; simp,
  have h0 : ∀ x y : F, x + 1 + (y + 1) = x + y :=
    by intros x y; rw [add_add_add_comm, char_two.add_self_eq_zero, add_zero],
  have h1 := fn_corr_lem2 F f feq h,
  rw [h0, ← h0 x y, ← h1, ← h1, ← h1, feq],
  apply congr_arg; ring,
end

theorem fn_corr2 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq2 F (f + 1) :=
begin
  intros feq h x; simp,
  apply fn_corr_lem2 F f feq h,
end

theorem fn_corr3 (f : F → F) :
  fn_eq1 F f → fn_eq2 F f → fn_eq F (f + 1) :=
begin
  intros feq1 feq2 x y; simp,
  have h0 : ∀ x y : F, x + 1 + (y + 1) = x + y :=
    by intros x y; rw [add_add_add_comm, char_two.add_self_eq_zero, add_zero],
  rw [h0, ← h0 x y, ← feq2, ← feq2, ← feq2, feq1],
  apply congr_arg,
  calc (x + 1) * (y + 1) + (x + 1) + (y + 1) = (x + 2) * (y + 2) - 1 : by ring
  ... = x * y - 1 : by rw [char_two.two_eq_zero, add_zero, add_zero]
  ... = x * y + 1 : by rw sub_eq_add,
end

end correspondence



---- Solution for the new FE system with char(F) = 2
---- We will write partial progress; we have no real full solution yet
namespace solution

variable f : F → F
variable feq1 : fn_eq1 F f
variable feq2 : fn_eq2 F f
include feq1 feq2



---- Start with basic lemmas, some transferred from general case by correspondence
lemma fn_lem1_1 :
  f + 1 ≠ 0 :=
begin
  intros h,
  rw [← sub_eq_add, sub_eq_zero] at h,
  suffices : 1 = (0 : F),
  { exact one_ne_zero this, },
  calc 1 = f (0 + 1) : by rw h; simp
  ... = f 0 + 1 : by rw feq2
  ... = (1 : F) + 1 : by rw h; simp
  ... = 0 : by rw char_two.add_self_eq_zero,
end

lemma fn_lem1_2 :
  f 0 = 0 :=
begin
  have X := correspondence.fn_corr3 F f feq1 feq2,
  have h := general.fn_lem3_4 F (f + 1) X,
  simp at h,
  rwa [← feq2, char_two.add_self_eq_zero] at h,
end

lemma fn_lem1_3 :
  f 1 = 1 :=
begin
  calc f 1 = f (0 + 1) : by rw zero_add
  ... = f 0 + 1 : by rw feq2
  ... = 0 + 1 : by rw fn_lem1_2 F f feq1 feq2
  ... = 1 : by rw zero_add,
end

lemma fn_lem1_4 :
  ∀ x : F, f x = 0 ↔ x = 0 :=
begin
  intros x,
  have X := correspondence.fn_corr3 F f feq1 feq2,
  have X0 := fn_lem1_1 F f feq1 feq2,
  have h := general.fn_thm3 F (f + 1) X X0,
  calc f x = 0 ↔ f x + 1 = 0 + 1 : by rw add_left_inj
  ... ↔ f (x + 1) = 1 : by rw [zero_add, feq2]
  ... ↔ f (x + 1) + 1 = 0 : by rw [← sub_eq_zero, sub_eq_add]
  ... ↔ (f + 1) (x + 1) = 0 : by simp
  ... ↔ x + 1 = 1 : _
  ... ↔ x = 0 : by rw [← sub_eq_zero, add_sub_cancel],
  { apply general.fn_thm3 F (f + 1),
    exact correspondence.fn_corr3 F f feq1 feq2,
    exact fn_lem1_1 F f feq1 feq2, },
end

--- The rest of the lemmas do not use A6_general
lemma fn_lem2_1 :
  ∀ x : F, f (f x) = f x :=
begin
  intros x,
  have h := feq1 x 1,
  rwa [mul_one, char_two.add_self_eq_zero, zero_add,fn_lem1_3 F f feq1 feq2,
       mul_one, ← sub_left_inj, add_sub_cancel, sub_eq_add, add_comm, feq2,
       add_assoc, char_two.add_self_eq_zero, add_zero] at h,
end

lemma fn_lem2_2 :
  ∀ x : F, f x = 1 ↔ x = 1 :=
begin
  intros x,
  calc f x = 1 ↔ f x + 1 = 0 : by rw [← sub_eq_zero, sub_eq_add]
  ... ↔ f (x + 1) = 0 : by rw ← feq2
  ... ↔ x + 1 = 0 : by rw fn_lem1_4 F f feq1 feq2
  ... ↔ x = 1 : by rw [← sub_eq_add, sub_eq_zero],
end

lemma fn_lem2_3 :
  ∀ x : F, f (x⁻¹) = (f x)⁻¹ :=
begin
  intros x,
  by_cases h : x = 0,
  { subst h,
    rw [inv_zero, fn_lem1_2 F f feq1 feq2, inv_zero], },
  have h0 := feq1 x x⁻¹,
  rw [mul_inv_cancel h, add_assoc, (add_comm (1 : F)), feq2,
      add_comm, add_right_inj, fn_lem2_2 F f feq1 feq2] at h0,
  rw inv_eq_of_mul_eq_one_right h0,
end

end solution







end case_char_eq_2



end IMO2017A6

