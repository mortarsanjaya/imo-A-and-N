import algebra.module.basic

namespace IMOSL
namespace IMO2019A1

variables {G : Type*} [add_comm_group G]

/--
  IMO 2019 A1 (P1), Generalized Version

  Let G be an abelian group, and take some T, U ∈ End(G).
  Here, End(G) is the set of endomorphisms of G.
  Let T and U be homomorphisms G → G.
  Suppose that U is injective.
  Determine all functions f : G → G such that, for all x, y ∈ G,
          f(Tx) + Uf(y) = f(f(x + y)).
  
  Answer:
    Fix some φ ∈ End(G) and C ∈ G such that φT = Uφ = φ^2 and φ(C) = U(C).
    Then x ↦ φ(x) + C satisfies the above equation.
    Furthermore, all functions satisfying the above equation are of this form.

  Solution:
    See https://www.imo-official.org/problems/IMO2019SL.pdf.
    We refer to the official Solution 2 and modify it for our generalization needs.
    
    Let f be an arbitrary function satisfying the above equation.
    Let C = f(0).
    As in the official Solution 2, we get both the following:
            ∀ x ∈ G, f(f(x)) = Uf(x) + C                      (1)
            ∀ x ∈ G, f(Tx) = U(f(x) - C) + C                  (2)
            ∀ x y ∈ G, f(x + y) = f(x) + f(y) - C             (3)
    Conversely, one can check that (1), (2), and (3) indeed implies the original equation.
    Thus, it remains to classify all functions f satisfying (1), (2), and (3).

    First notice that (3) is equivalent to f - C being additive.
    In particular, (3) means that we can write f = φ + C for some φ ∈ End(G).
    Then (2) reads as φT = Uφ and (1) becomes
            ∀ x : G, φ(φ(x) + C) = Uφ(x) + UC + C → φ^2(x) + φ(C) = Uφ(x) + UC
    Plugging in x = 0 yields φ(C) = UC.
    In turns, this implies that the above equation becomes φ^2 = Uφ.
    This shows that φT = Uφ = φ^2 and φ(C) = U(C).
  
  Note:
    For the case G = ℤ, see "A1_int.lean", theorem "final_solution_int".
    For the original case (T = U = 2), see theorem "final_solution_original" instead.
-/
def fn_eq (T U : add_monoid.End G) (f : G → G) := ∀ a b : G, f (T a) + U (f b) = f (f (a + b))



open function

namespace results

/-- Equation (1) -/
def fn_eq1 (U : add_monoid.End G) (f : G → G) (C : G) := ∀ x : G, f (f x) = U (f x) + C

/-- Equation (2) -/
def fn_eq2 (T U : add_monoid.End G) (f : G → G) (C : G) := ∀ x : G, f (T x) = U (f x - C) + C

/-- Equation (3) -/
def fn_eq3 (f : G → G) (C : G) := ∀ x y : G, f (x + y) = f x + f y - C

theorem feq_iff_feq123 (T U : add_monoid.End G) (U_inj : injective U) (f : G → G) :
  fn_eq T U f ↔ (fn_eq1 U f (f 0) ∧ fn_eq2 T U f (f 0) ∧ fn_eq3 f (f 0)) :=
begin
  split,
  --- fn_eq → fn_eq1 ∧ fn_eq2 ∧ fn_eq3
  { intros feq,
    have feq1 : fn_eq1 U f (f 0) :=
    begin
      intros x,
      have h := feq 0 x,
      rwa [T.map_zero, zero_add, add_comm, eq_comm] at h
    end,
    have feq2 : fn_eq2 T U f (f 0) :=
    begin
      intros x,
      have h := feq x 0,
      rwa [add_zero, feq1, ← eq_sub_iff_add_eq, add_sub_right_comm, ← U.map_sub] at h
    end,
    rw [and_iff_right feq1, and_iff_right feq2]; intros x y,
    have h := feq x y,
    rw [feq1, feq2, add_right_comm, add_left_inj, ← U.map_add, ← add_sub_right_comm, eq_comm] at h,
    exact U_inj h },
  ---- fn_eq1 → fn_eq2 → fn_eq3 → fn_eq
  { rintros ⟨feq1, feq2, feq3⟩ x y,
    rw [feq1, feq2, add_right_comm, add_left_inj, ← U.map_add, feq3, add_sub_right_comm] }
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

theorem feq2_hom_iff (T U φ : add_monoid.End G) (C : G) :
    fn_eq2 T U (φ + const G C) C ↔ φ * T = U * φ :=
  by simp only [fn_eq2, pi.add_apply, const_apply, add_sub_cancel, add_left_inj,
                add_monoid_hom.ext_iff, add_monoid.coe_mul, comp_app]

theorem feq1_hom_iff (U φ : add_monoid.End G) (C : G) :
  fn_eq1 U (φ + const G C) C ↔ (φ ^ 2 = U * φ ∧ φ C = U C) :=
begin
  rw [pow_two, add_monoid_hom.ext_iff],
  simp only [fn_eq1, pi.add_apply, const_apply, add_left_inj,
             φ.map_add, U.map_add, add_monoid.coe_mul, comp_app],
  split,
  { intros feq1,
    have h := feq1 0,
    rw [φ.map_zero, φ.map_zero, zero_add, U.map_zero, zero_add] at h,
    rw and_iff_left h; intros x,
    have h0 := feq1 x,
    rwa [h, add_left_inj] at h0 },
  { rintros ⟨h, h0⟩ x;
    rw [h0, h] }
end

end results



/-- Final solution -/
theorem final_solution_general (T U : add_monoid.End G) (U_inj : injective U) (f : G → G) :
  fn_eq T U f ↔ ∃ (φ : add_monoid.End G) (C : G),
    f = φ + const G C ∧ φ * T = U * φ ∧ φ ^ 2 = U * φ ∧ φ C = U C :=
begin
  rw [results.feq_iff_feq123 _ _ U_inj, results.feq3_iff_exists_hom_eq_f_sub_C]; split,
  { set C := f 0 with C_val,
    rintros ⟨feq1, feq2, φ, h⟩,
    rw [h, results.feq1_hom_iff] at feq1,
    rw [h, results.feq2_hom_iff] at feq2,
    use [φ, f 0]; split,
    rw [← C_val, ← h],
    split; assumption },
  { rintros ⟨φ, C, rfl, h, h0, h1⟩,
    rw [pi.add_apply, const_apply, φ.map_zero, zero_add,
        results.feq1_hom_iff, results.feq2_hom_iff],
    repeat { split }; assumption }
end

end IMO2019A1
end IMOSL
