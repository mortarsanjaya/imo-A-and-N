import algebra.module.basic

/-!
# IMO 2019 A1 (P1), Generalized Version

Let (G, +) be an abelian group.
Fix an arbitrary function g : G → G with g(0) = 0 and an injective endomorphism T of G.
Determine all functions f : G → G such that, for all x, y ∈ G,
  f(g(x)) + Tf(y) = f(f(x + y)).
  
## Answer

Fix some φ ∈ End(G) and C ∈ G such that φ ∘ h = Tφ = φ^2 and φ(C) = U(C).
Then x ↦ φ(x) + C satisfies the above equation.
Furthermore, all functions satisfying the above equation are of this form.

## Solution

See <https://www.imo-official.org/problems/IMO2019SL.pdf>.
We refer to the official Solution 2 and modify it for our generalization needs.
    
Let f be an arbitrary function satisfying the above equation.
Let C = f(0).
As in the official Solution 2, we get both the following:
  ∀ x ∈ G, f(f(x)) = Tf(x) + C                      (1)
  ∀ x ∈ G, f(g(x)) = T(f(x) - C) + C                (2)
  ∀ x y ∈ G, f(x + y) = f(x) + f(y) - C             (3)
Conversely, one can check that (1), (2), and (3) indeed implies the original equation.
Thus, it remains to classify all functions f satisfying (1), (2), and (3).

First notice that (3) is equivalent to f - C being additive.
In particular, (3) means that we can write f = φ + C for some φ ∈ End(G).
Then (2) reads as φ ∘ g = Tφ and (1) becomes
  ∀ x : G, φ(φ(x) + C) = Tφ(x) + T(C) + C → φ^2(x) + φ(C) = Tφ(x) + T(C)
Plugging in x = 0 yields φ(C) = T(C).
In turn, this implies that the above equation becomes φ^2 = Tφ.
This shows that φ ∘ g = Tφ = φ^2 and φ(C) = T(C).
  
## Notes

* For the case G = ℤ, see "A1_int.lean", theorem "final_solution_int".
* For the original case (T = 2 and g = x ↦ 2x), see theorem "final_solution_original" instead.
-/

open function

namespace IMOSL
namespace IMO2019A1

variables {G : Type*} [add_comm_group G]

def fn_eq (g : G → G) (T : add_monoid.End G) (f : G → G) :=
  ∀ a b : G, f (g a) + T (f b) = f (f (a + b))



namespace results

/-- Equation (1) -/
def fn_eq1 (T : add_monoid.End G) (f : G → G) (C : G) :=
  ∀ x : G, f (f x) = T (f x) + C

/-- Equation (2) -/
def fn_eq2 (g : G → G) (T : add_monoid.End G) (f : G → G) (C : G) :=
  ∀ x : G, f (g x) = T (f x - C) + C

/-- Equation (3) -/
def fn_eq3 (f : G → G) (C : G) :=
  ∀ x y : G, f (x + y) = f x + f y - C



theorem feq_iff_feq123 {g : G → G} (g_zero : g 0 = 0)
    {T : add_monoid.End G} (T_inj : injective T) (f : G → G) :
  fn_eq g T f ↔ (fn_eq1 T f (f 0) ∧ fn_eq2 g T f (f 0) ∧ fn_eq3 f (f 0)) :=
begin
  split,
  --- fn_eq → fn_eq1 ∧ fn_eq2 ∧ fn_eq3
  { intros feq,
    rw and_iff_left_of_imp,
    { intros x,
      have h := feq 0 x,
      rwa [g_zero, zero_add, add_comm, eq_comm] at h },
    intros feq1,
    rw and_iff_left_of_imp,
    { intros x,
      have h := feq x 0,
      rwa [add_zero, feq1, ← eq_sub_iff_add_eq, add_sub_right_comm, ← T.map_sub] at h },
    intros feq2 x y,
    have h := feq x y,
    rw [feq1, feq2, add_right_comm, add_left_inj, ← T.map_add, ← add_sub_right_comm, eq_comm] at h,
    exact T_inj h },
  ---- fn_eq1 → fn_eq2 → fn_eq3 → fn_eq
  { rintros ⟨feq1, feq2, feq3⟩ x y,
    rw [feq1, feq2, add_right_comm, add_left_inj, ← T.map_add, feq3, add_sub_right_comm] }
end

theorem feq3_iff_exists_hom_eq_f_sub_C (f : G → G) (C : G) :
  fn_eq3 f C ↔ ∃ φ : add_monoid.End G, f = φ + const G C :=
begin
  split,
  { intros feq3,
    use f - const G C,
    have h := feq3 0 0,
    rw [add_zero, eq_sub_iff_add_eq, add_right_inj] at h,
    rw [pi.sub_apply, const_apply, h, sub_self],
    intros x y; simp only [const_apply, pi.sub_apply],
    rw [feq3, sub_sub, add_sub_add_comm],
    rw [add_monoid_hom.coe_mk, sub_add_cancel] },
  { rintros ⟨φ, rfl⟩ x y,
    simp only [pi.add_apply, const_apply],
    rw [← add_assoc, add_sub_cancel, add_right_comm, φ.map_add] }
end

theorem feq2_hom_iff (g : G → G) (T φ : add_monoid.End G) (C : G) :
  fn_eq2 g T (φ + const G C) C ↔ φ ∘ g = ⇑(T * φ) :=
begin
  rw [add_monoid.coe_mul, funext_iff],
  simp only [fn_eq2, pi.add_apply, const_apply, add_sub_cancel, add_left_inj]
end

theorem feq1_hom_iff (T φ : add_monoid.End G) (C : G) :
  fn_eq1 T (φ + const G C) C ↔ (φ ^ 2 = T * φ ∧ φ C = T C) :=
begin
  rw [pow_two, add_monoid_hom.ext_iff],
  simp only [fn_eq1, const_apply, pi.add_apply, comp_app, add_monoid.coe_mul, add_left_inj],
  symmetry; split,
  rintros ⟨h, h0⟩ x; rw [φ.map_add, h0, h, T.map_add],
  intros feq1,
  have h := feq1 0,
  rw [φ.map_zero, zero_add] at h,
  rw and_iff_left h; intros x,
  rw [← add_left_inj (φ C), ← φ.map_add, feq1, h, T.map_add],
end

end results



/-- Final solution -/
theorem final_solution_general {g : G → G} (g_zero : g 0 = 0)
    {T : add_monoid.End G} (T_inj : injective T) (f : G → G) :
  fn_eq g T f ↔ ∃ (φ : add_monoid.End G) (C : G),
    f = φ + const G C ∧ φ ∘ g = ⇑(T * φ) ∧ φ ^ 2 = T * φ ∧ φ C = T C :=
begin
  rw [results.feq_iff_feq123 g_zero T_inj, results.feq3_iff_exists_hom_eq_f_sub_C],
  split,
  { set C := f 0 with C_val,
    rintros ⟨feq1, feq2, φ, h⟩; use [φ, C],
    rw [h, results.feq1_hom_iff] at feq1,
    rw [and_iff_right h, and_iff_left feq1],
    rwa [h, results.feq2_hom_iff] at feq2 },
  { rintros ⟨φ, C, rfl, h, h0, h1⟩,
    rw [pi.add_apply, const_apply, φ.map_zero, zero_add, results.feq1_hom_iff, and_assoc,
        and_iff_right h0, and_iff_right h1, results.feq2_hom_iff, and_iff_right h],
    use φ }
end

end IMO2019A1
end IMOSL
