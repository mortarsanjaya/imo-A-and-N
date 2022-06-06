import
  IMO2017.A6.A6_char_eq_2.basic
  algebra.char_p.pi

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]



namespace case_char_eq_2

open char_two

variable [char_p F 2]







---- Solution for the new FE system with char(F) = 2
---- We will write partial progress; we have no real full solution yet
namespace base_lemma

variable f : F → F
variable feq1 : fn_eq1 F f
variable feq2 : fn_eq2 F f
include feq1 feq2



---- Results transferred from general case
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
  have X := correspondence.fn_thm3 F f feq1 feq2,
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
  have X := correspondence.fn_thm3 F f feq1 feq2,
  have X0 := fn_lem1_1 F f feq1 feq2,
  have h := general.fn_thm3 F (f + 1) X X0,
  calc f x = 0 ↔ f x + 1 = 0 + 1 : by rw add_left_inj
  ... ↔ f (x + 1) = 1 : by rw [zero_add, feq2]
  ... ↔ f (x + 1) + 1 = 0 : by rw [← sub_eq_zero, sub_eq_add]
  ... ↔ (f + 1) (x + 1) = 0 : by simp
  ... ↔ x + 1 = 1 : _
  ... ↔ x = 0 : by rw [← sub_eq_zero, add_sub_cancel],
  { apply general.fn_thm3 F (f + 1),
    exact correspondence.fn_thm3 F f feq1 feq2,
    exact fn_lem1_1 F f feq1 feq2, },
end



---- More results specialized for case char(F) = 2
lemma fn_lem2_1 :
  ∀ x : F, f (f x) = f x :=
begin
  intros x,
  have h := feq1 x 1,
  rwa [mul_one, char_two.add_self_eq_zero, zero_add, fn_lem1_3 F f feq1 feq2,
       mul_one, ← eq_sub_iff_add_eq, sub_eq_add, add_comm, feq2, add_assoc,
       char_two.add_self_eq_zero, add_zero] at h,
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

lemma fn_lem2_4 : 
  ∀ x y : F, f (f x * f y) + f (x + y) + 1 = f ((x + 1) * (y + 1)) :=
begin
  intros x y,
  rw [feq1, ←feq2],
  apply congr_arg,
  ring,
end

lemma fn_lem2_5 (a b : F) (h : f a = f b) :
  ∀ x : F, f (a * x) + f (a + x) = f(b * x) + f (b + x) :=
begin
  suffices : ∀ x y : F, f (x * y) + f (x + y) = f (f (x + 1) * f (y + 1)) + 1,
  { intros x,
    have h0 : f (a + 1) = f (b + 1) := by rw [feq2, feq2, h],
    rw [this, h0, ← this], },
  intros x y,
  have h0 : x + 1 + (y + 1) = x + y :=
    by rw [add_add_add_comm, char_two.add_self_eq_zero, add_zero],
  rw [← eq_sub_iff_add_eq, sub_eq_add, add_right_comm, ← h0, feq1, ← feq2],
  apply congr_arg,
  rw [← sub_eq_add x, ← sub_eq_add y],
  ring,
end

end solution







end case_char_eq_2

end IMO2017A6