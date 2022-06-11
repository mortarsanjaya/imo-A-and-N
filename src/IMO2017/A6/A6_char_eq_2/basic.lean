import
  IMO2017.A6.A6_general
  algebra.char_p.two
  algebra.char_p.pi

namespace IMO2017A6

universe u
variable {F : Type u}
variable [field F]

/-
  Progress of 2017 A6 for the case char(F) = 2

  Here, we give an alternative FE system.
  We also give correspondence results between the two FE systems.
  Then, we prove basic lemmas about the new FE system.
-/

def fn_eq1 (f : F → F) :=
  ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y + x + y)
def fn_eq2 (f : F → F) :=
  ∀ x : F, f (x + 1) = f x + 1







namespace case_char_eq_2

open char_two

variable [char_p F 2]



---- Correspondence between the new FE and the old FE, excluding the case where f = 0
namespace correspondence

lemma fn_lem1 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  f 0 = 1 :=
begin
  apply frobenius_inj F 2,
  have h0 := general.fn_lem3_3 feq h,
  unfold frobenius; rw [ring_hom.coe_mk, h0, one_pow],
end

lemma fn_lem2 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  fn_eq2 f :=
begin
  intros x,
  rw [general.fn_lem4_1 feq (fn_lem1 h feq), sub_eq_add],
end

theorem fn_thm1 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  fn_eq1 (λ x, f (x + 1)) :=
begin
  have feq2 := fn_lem2 h feq, 
  intros x y; simp only [],
  rw [feq2, add_assoc, add_comm 1 (f _), ← feq2, add_right_comm x, add_assoc,
      feq, add_mul, one_mul, mul_add, mul_one, ← add_assoc],
end

theorem fn_thm2 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  fn_eq2 (λ x, f (x + 1)) :=
begin
  intros x; simp only [],
  exact fn_lem2 h feq (x + 1),
end

theorem fn_thm3 {f : F → F} (feq1 : fn_eq1 f) (feq2 : fn_eq2 f) :
  fn_eq (λ x, f (x + 1)) :=
begin
  intros x y; simp only [],
  rw [feq2, add_assoc, add_comm 1 (f _), ← feq2, add_right_comm x, add_assoc, feq1],
  apply congr_arg; symmetry,
  calc x * y + 1 = (x + 1 - 1) * y + 1 : by rw add_sub_cancel
  ... = (x + 1 + 1) * y + 1 : by rw sub_eq_add
  ... = (x + 1) * y + y + 1 : by rw [add_mul, one_mul]
  ... = (x + 1) * y + (y + 1) : by rw add_assoc
  ... = (x + 1) * (y + 1 - 1) + (y + 1) : by rw add_sub_cancel
  ... = (x + 1) * (y + 1 + 1) + (y + 1) : by rw sub_eq_add
  ... = (x + 1) * (y + 1) + (x + 1) + (y + 1) : by rw [mul_add, mul_one],
end

theorem fn_corr {f : F → F} (h : f ≠ 0) :
  fn_eq f ↔ (fn_eq1 (λ x, f (x + 1)) ∧ fn_eq2 (λ x, f (x + 1))) :=
begin
  split,
  { intros feq; split,
    exact fn_thm1 h feq,
    exact fn_thm2 h feq },
  { intros h0; cases h0 with feq1 feq2,
    have h1 := fn_thm3 feq1 feq2,
    simp only [] at h1,
    suffices : (λ x, f (x + 1 + 1)) = f,
      rwa ← this,
    apply funext; intros x,
    rw [← sub_eq_add, add_sub_cancel] },
end

end correspondence



---- More base lemmas for the new FE system
namespace base_lemma

variable {f : F → F}
variable feq1 : fn_eq1 f
variable feq2 : fn_eq2 f
include feq1 feq2



---- Results transferred from general case
lemma fn_lem1_1 :
  f 0 = 0 :=
begin
  have h := general.fn_lem3_4 (correspondence.fn_thm3 feq1 feq2),
  simp only [] at h,
  rwa char_two.add_self_eq_zero at h,
end

lemma fn_lem1_2 :
  f 1 = 1 :=
begin
  calc f 1 = f (0 + 1) : by rw zero_add
  ... = f 0 + 1 : by rw feq2
  ... = 0 + 1 : by rw fn_lem1_1 feq1 feq2
  ... = 1 : by rw zero_add,
end

lemma fn_lem1_3 :
  ∀ x : F, f x = 0 ↔ x = 0 :=
begin
  intros x,
  calc f x = 0 ↔ f (x + 1 + 1) = 0 : by rw [← sub_eq_add, add_sub_cancel]
  ... ↔ x + 1 = 1 : _
  ... ↔ x = 0 : by rw add_left_eq_self,
  { rw general.fn_thm3 (correspondence.fn_thm3 feq1 feq2),
    intros h,
    have h0 : f (0 + 1) = (0 : F → F) 0 := by rw ← h; simp only [],
    rw [zero_add, pi.zero_apply, fn_lem1_2 feq1 feq2] at h0,
    exact one_ne_zero h0 },
end



---- More results specialized for case char(F) = 2
lemma fn_lem2_1 :
  ∀ x : F, f (f x) = f x :=
begin
  intros x,
  have h := feq1 x 1,
  rwa [mul_one, char_two.add_self_eq_zero, zero_add, fn_lem1_2 feq1 feq2,
       mul_one, feq2, ← add_assoc, add_left_eq_self, ← sub_eq_add, sub_eq_zero] at h,
end

lemma fn_lem2_2 :
  ∀ x : F, f x = 1 ↔ x = 1 :=
begin
  intros x,
  calc f x = 1 ↔ f x + 1 = 0 : by rw [← sub_eq_zero, sub_eq_add]
  ... ↔ f (x + 1) = 0 : by rw ← feq2
  ... ↔ x + 1 = 0 : by rw fn_lem1_3 feq1 feq2
  ... ↔ x = 1 : by rw [← sub_eq_add, sub_eq_zero],
end

lemma fn_lem2_3 :
  ∀ x : F, f (x⁻¹) = (f x)⁻¹ :=
begin
  intros x,
  by_cases h : x = 0,
  rw [h, inv_zero, fn_lem1_1 feq1 feq2, inv_zero],
  have h0 := feq1 x x⁻¹,
  rw [mul_inv_cancel h, add_assoc, (add_comm (1 : F)), feq2,
      add_comm, add_right_inj, fn_lem2_2 feq1 feq2] at h0,
  rw inv_eq_of_mul_eq_one_right h0,
end

lemma fn_lem2_4 : 
  ∀ x y : F, f (f x * f y) + f (x + y) + 1 = f ((x + 1) * (y + 1)) :=
begin
  intros x y,
  rw [feq1, ← feq2, add_mul, one_mul, mul_add, mul_one, ← add_assoc],
end

lemma fn_lem2_5 :
  ∀ x y : F, f ((f x + 1) * (f y + 1)) + 1 = f (x * y) + f (x + y) :=
begin
  intros x y,
  have h := fn_lem2_4 feq1 feq2 (x - 1) (y - 1),
  rwa [sub_add_cancel, sub_add_cancel, sub_add_sub_comm, char_two.add_self_eq_zero,
      sub_zero, add_right_comm, ← eq_sub_iff_add_eq, sub_eq_add, sub_eq_add,
      sub_eq_add, feq2, feq2] at h,
end

lemma fn_lem2_6 {a b : F} (h : f a = f b) :
  ∀ x : F, f (a * x) + f (a + x) = f(b * x) + f (b + x) :=
begin
  intros x,
  rw [← fn_lem2_5 feq1 feq2, h, fn_lem2_5 feq1 feq2 ],
end

lemma fn_lem2_7 {a b c d : F} (h : f a = f b) (h0 : f c = f d) :
  f (a * c) + f (a + c) = f(b * d) + f (b + d) :=
begin
  rw [fn_lem2_6 feq1 feq2 h, add_comm b, mul_comm,
      fn_lem2_6 feq1 feq2 h0, add_comm d, mul_comm],
end



end base_lemma







end case_char_eq_2



end IMO2017A6
