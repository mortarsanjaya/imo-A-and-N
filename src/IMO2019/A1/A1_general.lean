import
  algebra.group.basic
  algebra.module.torsion
  algebra.hom.group
  group_theory.torsion


namespace IMO2019A1

universe u
variable {G : Type u}
variable [add_comm_group G]

/--
  IMO 2019 A1 (P1), Generalized Version

  Let G be a 2-torsion-free abelian group.
  Determine all functions f : G → G such that, for all a, b ∈ G,
          f(2a) + 2 f(b) = f(f(a + b)).

  The only solutions to the case G = ℤ are n ↦ 0 and x ↦ 2n + C for some constant C.
  However, there is a more general functions satisfying the above equation.

  The proof for the original version with G = ℤ is in the file "A1_int.lean".
  See theorem "final_solution_int".

  Answer:
    Fix some φ ∈ End(G) with φ² = id, and fix a fixed point C of φ.
    Then, x ↦ φ(x) + x + C satisfies the above equation.
    Furthermore, all functions satisfying the above equation are of this form.

  Solution:
    See https://www.imo-official.org/problems/IMO2011SL.pdf.
    We refer to the official Solution 2 and modify it for our generalization needs.
    
    Let f be an arbitrary function satisfying the above equation.
    Let C = f(0).
    As in the official Solution 2, we get both the following:
            ∀ b ∈ G, f(f(b)) = 2 f(b) + C                     (1)
            ∀ a ∈ G, f(2a) = 2 f(a) - C
            ∀ a b ∈ G, f(a + b) = f(a) + f(b) - C             (2)
    Conversely, one can check that (1) and (2) indeed implies the original equation.
    Thus, it remains to classify all functions f satisfying (1) and (2).

    Now, let φ = x ↦ f(x) - (x + C).
    By the second equation, φ is an endomorphism of G.
    The first equation now tells us that, for all b ∈ G,
            φ(f(b)) = f(b)
            φ²(b) + φ(b) + φ(C) = φ(b) + b + C
            φ²(b) + φ(C) = b + C
    Plugging in b = 0 yields φ(C) = C, which implies φ² = id.
    This shows that we have f(x) = φ(x) + x + C with φ² = id and φ(C) = C.
    In particular, φ is an automorphism of G of order at most 2.

    Conversely, one can check that, for any φ ∈ End(G) with φ² = id,
      the map x ↦ φ(x) + x + C indeed satisfies (1) and (2).
    The latter is trivial, so we just check for the former:
            f(f(b)) = 2 f(b) + C ↔ φ(f(b)) = f(b).
    And indeed the latter equation holds since φ² = id and φ(C) = C.
  
  Note:
  1. The solution indeed generalizes the case G = ℤ.
     The only group automorphisms of ℤ are id and x ↦ -x.
     In the former case, C is arbitrary, giving us f = x ↦ 2x + C.
     In the latter case, we force C = 0 and φ = 0, giving us f = 0.

  2. Obtaining (2) requires G to be 2-torsion-free.
     However, (1) and f(2a) = 2 f(a) - C does not require G to be 2-torsion-free.
     Thus, we will include the 2-torsion-free criterion rather moderately.
-/
def fn_eq (f : G → G) :=
  ∀ a b : G, f (2 • a) + 2 • f b = f (f (a + b))







open function

namespace results



/-- Equation (1) -/
@[protected]
def fn_eq1 (f : G → G) (C : G) :=
  ∀ a : G, f (f a) = 2 • f a + C

/-- Equation (2) -/
@[protected]
def fn_eq2 (f : G → G) (C : G) :=
  ∀ a b : G, f (a + b) = f a + f b - C



---- Here, we prove that feq holds if and only if (1) and (2) holds.
section iff_cond

lemma fn_lem1_1 {f : G → G} (feq : fn_eq f) :
  fn_eq1 f (f 0) :=
begin
  intros b,
  have h := feq 0 b,
  rwa [zero_add, smul_zero, add_comm, eq_comm] at h,
end

lemma fn_lem1_2 {f : G → G} (feq : fn_eq f) :
  ∀ a : G, f (2 • a) = 2 • f a - f 0 :=
begin
  intros a,
  have h := feq a 0,
  rwa [add_zero, fn_lem1_1 feq, ← eq_add_neg_iff_add_eq, ← zsmul_neg_coe_of_pos _ zero_lt_two,
       add_assoc, ← one_add_zsmul, int.coe_nat_succ, int.coe_nat_one, ← sub_eq_add_neg,
       ← sub_sub, sub_self, zero_sub, neg_one_smul, ← sub_eq_add_neg] at h,
end

lemma fn_lem1_3 (two_torsion_free : submodule.torsion_by ℕ G 2 = ⊥)
    {f : G → G} (feq : fn_eq f) :
  fn_eq2 f (f 0) :=
begin
  intros a b,
  have h := feq a b,
  rwa [add_comm, fn_lem1_1 feq, fn_lem1_2 feq, add_sub, sub_eq_iff_eq_add, ← smul_add,
       add_assoc, ← two_smul ℕ (f 0), ← smul_add, eq_comm, ← sub_eq_zero, ← smul_sub,
       ← submodule.mem_torsion_by_iff, two_torsion_free, submodule.mem_bot, sub_eq_zero,
       add_comm (f b), ← eq_sub_iff_add_eq] at h,
end

lemma fn_lem1_4 {f : G → G} (feq1 : fn_eq1 f (f 0)) (feq2 : fn_eq2 f (f 0)) :
  fn_eq f :=
begin
  intros a b,
  rw [add_comm, feq1, feq2, two_smul ℕ a, feq2, ← two_smul ℕ (f a), add_sub, ← smul_add,
      add_comm, sub_eq_iff_eq_add, add_assoc, ← two_smul ℕ (f 0), ← smul_add, sub_add_cancel],
end

theorem fn_thm1 (two_torsion_free : submodule.torsion_by ℕ G 2 = ⊥) (f : G → G) :
  fn_eq f ↔ (fn_eq1 f (f 0) ∧ fn_eq2 f (f 0)) :=
begin
  split,
  intros h; split,
  exact fn_lem1_1 h,
  exact fn_lem1_3 two_torsion_free h,
  intros h; cases h with h h0,
  exact fn_lem1_4 h h0,
end

end iff_cond



---- Now we describe all functions satisfying (1) and (2).
section description

lemma fn_lem2_1 {f : G → G} {C : G} (feq2 : fn_eq2 f C) :
  ∃ g : add_monoid.End G, f = g + const G C :=
begin
  have h := feq2 0 0,
  rw [add_zero, eq_sub_iff_add_eq, add_right_inj] at h,
  use f - const G C,
  rw [pi.sub_apply, const_apply, h, sub_self],
  intros x y,
  simp only [pi.sub_apply, const_apply],
  rw [feq2, sub_add_sub_comm, sub_sub],
  rw [add_monoid_hom.coe_mk, sub_add_cancel],
end

lemma fn_lem2_2 (φ : add_monoid.End G) (C : G) :
  fn_eq2 (φ + const G C) C :=
begin
  intros a b,
  simp only [pi.add_apply, const_apply],
  rw [add_monoid_hom.map_add, ← add_sub, add_sub_cancel, add_right_comm],
end

lemma fn_lem2_3 {g : add_monoid.End G} {C : G}
    (feq1 : fn_eq1 (g + const G C) C) :
  ∃ (φ : add_monoid.End G), g = φ + 1 ∧ φ C = C ∧ φ ^ 2 = 1 :=
begin
  let φ := g - 1,
  use φ; split,
  rw sub_add_cancel,
  have h : ∀ a : G, (φ ^ 2) a + φ C = a + C,
  { intros a,
    have h := feq1 a,
    simp only [pi.add_apply, const_apply] at h,
    rw [add_left_inj, smul_add, add_monoid_hom.map_add, ← eq_sub_iff_add_eq,
        ← add_sub, add_comm, ← sub_eq_iff_eq_add] at h,
    rw [add_monoid.End.coe_pow, iterate_succ, iterate_one, comp_app],
    simp only [add_monoid.coe_one, id.def, add_monoid_hom.sub_apply],
    rw [add_monoid_hom.map_sub, ← sub_add, sub_sub, ← two_smul ℕ (g a), h, add_comm _ a,
        add_assoc, add_right_inj, add_sub, sub_add_cancel, two_smul ℕ, add_sub_cancel] },
  have h0 := h 0,
  rw [zero_add, add_monoid_hom.map_zero, zero_add] at h0,
  split,
  exact h0,
  rw add_monoid_hom.ext_iff; intros a,
  have h1 := h a,
  rwa [h0, add_left_inj] at h1,
end

lemma fn_lem2_4 {φ : add_monoid.End G} (h : φ ^ 2 = 1) {C : G} (h0 : φ C = C) :
  fn_eq ((φ + 1 : add_monoid.End G) + const G C) :=
begin
  apply fn_lem1_4,

  ---- First prove fn_eq1
  { intros a,
    simp only [const_apply, add_zero, id.def, pi.add_apply],
    have h1 : φ (φ a) = a :=
      by rw [← comp_app φ, ← iterate_one φ, ← iterate_add,
             ← add_monoid.End.coe_pow, h, add_monoid.coe_one, id_def],
    simp_rw [add_monoid_hom.add_apply],
    simp only [add_monoid.coe_one, id_def],
    rw [add_monoid_hom.map_zero, zero_add, zero_add, add_left_inj, add_monoid_hom.map_add,
        h0, add_monoid_hom.map_add, h1, add_comm _ (φ a), ← two_smul ℕ] },

  ---- Now prove fn_eq2
  { rw [pi.add_apply, const_apply, add_monoid_hom.map_zero, zero_add],
    exact fn_lem2_2 (φ + 1) C },
end

end description



end results







theorem final_solution_general (two_torsion_free : submodule.torsion_by ℕ G 2 = ⊥) :
  set_of fn_eq =
    (λ (s : add_monoid.End G × G), (s.fst + 1 : add_monoid.End G) + const G s.snd) ''
      {s | s.fst ^ 2 = 1 ∧ s.fst s.snd = s.snd} :=
begin
  rw set.ext_iff; intros f,
  rw [set.mem_set_of_eq, set.mem_image, prod.exists],
  simp only [add_monoid_hom.coe_mk, set.mem_set_of_eq]; split,

  ---- All functions satisfying fn_eq are in the RHS set
  { intros feq,
    have feq1 := results.fn_lem1_1 feq,
    have feq2 := results.fn_lem1_3 two_torsion_free feq,
    set C := f 0,
    cases results.fn_lem2_1 feq2 with g h,
    rw h at feq1,
    rcases results.fn_lem2_3 feq1 with ⟨φ, h0, h1, h2⟩,
    use [φ, C]; split,
    split; assumption,
    rw [← h0, ← h] },

  ---- All functions on the RHS satisfy fn_eq
  { intros h,
    rcases h with ⟨φ, C, ⟨h, h0⟩, h1⟩,
    rw ← h1; exact results.fn_lem2_4 h h0 },
end

end IMO2019A1
