import
  IMO2017.A6.A6_general
  algebra.char_p.two

/-
  Progress of 2017 A6 for the case char(F) = 2

  Here, we give an alternative FE system.
  We also give correspondence results between the two FE systems.
-/

namespace IMO2017A6

universe u
variable F : Type u
variable [field F]



namespace case_char_eq_2

open char_two

variable [char_p F 2]







---- Start with new definitions
def fn_eq1 (f : F → F) := ∀ x y : F, f (f x * f y) + f (x + y) = f (x * y + x + y)
def fn_eq2 (f : F → F) := ∀ x : F, f (x + 1) = f x + 1



---- Correspondence between the new FE and the old FE
---- (Exclude the case where f = 0)
namespace correspondence

lemma fn_lem1 (f : F → F) :
  fn_eq F f → f ≠ 0 → f 0 = 1 :=
begin
  intros feq h,
  rw [← sub_eq_zero, ← sq_eq_zero_iff, sub_eq_add,
      char_two.add_sq, general.fn_lem3_3 F f feq h],
  simp,
end

lemma fn_lem2 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq2 F f :=
begin
  intros feq h x,
  rw [general.fn_lem4_1 F f feq (fn_lem1 F f feq h), sub_eq_add],
end

theorem fn_thm1 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq1 F (f + 1) :=
begin
  intros feq h x y; simp,
  have h0 : ∀ x y : F, x + 1 + (y + 1) = x + y :=
    by intros x y; rw [add_add_add_comm, char_two.add_self_eq_zero, add_zero],
  have h1 := fn_lem2 F f feq h,
  rw [h0, ← h0 x y, ← h1, ← h1, ← h1, feq],
  apply congr_arg; ring,
end

theorem fn_thm2 (f : F → F) :
  fn_eq F f → f ≠ 0 → fn_eq2 F (f + 1) :=
begin
  intros feq h x; simp,
  apply fn_lem2 F f feq h,
end

theorem fn_thm3 (f : F → F) :
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







end case_char_eq_2



end IMO2017A6

