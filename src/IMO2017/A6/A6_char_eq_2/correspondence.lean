import IMO2017.A6.A6_general IMO2017.A6.A6_char_eq_2.basic algebra.char_p.two algebra.char_p.pi

/-!
## Progress of 2017 A6 for the case char(F) = 2

Here, we deal with an alternative FE system as follows:
  ∀ x y ∈ F, f(f(x) f(y)) + f(x + y) = f(xy + x + y)
  ∀ x ∈ F, f(x + 1) = f(x) + 1
-/

open char_two
open_locale classical

namespace IMOSL
namespace IMO2017A6

variables {F : Type*} [field F] [char_p F 2]




---- Correspondence between the new FE and the old FE, excluding the case where f = 0
namespace correspondence

lemma fn_lem1 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  f 0 = 1 :=
begin
  apply frobenius_inj F 2,
  have h0 := results.fn_general3_3 feq h,
  unfold frobenius; rw [ring_hom.coe_mk, h0, one_pow],
end

lemma fn_lem2 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  fn_eq2 f :=
begin
  intros x,
  rw [results.fn_general4_1 feq (fn_lem1 h feq), sub_eq_add],
end

theorem fn_thm1 {f : F → F} (h : f ≠ 0) (feq : fn_eq f) :
  fn_eq1 (λ x, f (x + 1)) :=
begin
  have feq2 := fn_lem2 h feq,
  intros x y; simp only [],
  rw [feq2, add_assoc, add_comm 1 (f _), ← feq2, add_right_comm x,
      add_assoc, feq, add_one_mul, mul_add_one, ← add_assoc],
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
  rw [feq2, add_assoc, add_comm 1 (f _), ← feq2, add_right_comm x, add_assoc,
      feq1, ← mul_add_one, ← sub_eq_add (y + 1) 1, add_sub_cancel, ← add_assoc,
      ← add_one_mul, ← sub_eq_add (x + 1) 1, add_sub_cancel],
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

end IMO2017A6
end IMOSL
