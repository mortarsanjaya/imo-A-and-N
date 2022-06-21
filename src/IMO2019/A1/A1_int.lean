import
  IMO2019.A1.A1_general
  data.int.basic

namespace IMO2019A1

/-
  IMO 2019 A1 (P1), Original Version

  Solution:
  From the generalized version, all functions satisfying the equation are of form
    x ↦ φ(x) + x + C for some φ ∈ End(ℤ) with φ² = 1 and C ∈ G with φ(C) = C.
  However, the only φ ∈ End(ℤ) with φ² = 1 are id and x ↦ -x.
  For the former case, we get f(x) = 2x + C.
  For the latter case, C = 0 is forced and we get f = 0.

  Implementation details:
    One has to show that the only possible such endomorphisms are indeed id and x ↦ -x.
    Also, one has to show that ℤ is 2-torsion-free.
-/

open set
open function



namespace extra

lemma nat_int_two_torsion_free :
  submodule.torsion_by ℕ ℤ 2 = ⊥ :=
begin
  apply submodule.ext; intros x,
  rw [submodule.mem_torsion_by_iff, submodule.mem_bot, nsmul_eq_zero_iff],
  exact two_ne_zero,
end

lemma int_End_description (φ : add_monoid.End ℤ) :
  ∀ x : ℤ, φ x = φ 1 * x :=
begin
  suffices : ∀ n : ℕ, φ ↑n = φ 1 * ↑n,
  { intros n,
    rcases int.eq_coe_or_neg n with ⟨m, h | h⟩,
    rw [h, this],
    rw [h, add_monoid_hom.map_neg, this, mul_neg] },
  intros n; induction n with n n_ih,
  rw [int.coe_nat_zero, mul_zero, add_monoid_hom.map_zero],
  rw [int.coe_nat_succ, add_monoid_hom.map_add, n_ih, mul_add_one],
end

lemma int_end_sq_eq_one (φ : add_monoid.End ℤ) :
  φ ^ 2 = 1 ↔ φ = 1 ∨ φ = -1 :=
begin
  symmetry; split,
  intros h; cases h with h h,
  rw [h, one_pow],
  rw [h, neg_pow_two, one_pow],
  intros h,
  rw add_monoid_hom.ext_iff at h,
  have h0 := h 1,
  rw [add_monoid.coe_one, id.def, add_monoid.End.coe_pow, iterate_succ,
      iterate_one, comp_app, int_End_description, mul_self_eq_one_iff] at h0,
  cases h0 with h0 h0,
  left; rw add_monoid_hom.ext_iff; intros x,
  rw [add_monoid.coe_one, id.def, int_End_description, h0, one_mul],
  right; rw add_monoid_hom.ext_iff; intros x,
  rw [add_monoid_hom.neg_apply, add_monoid.coe_one,
      id.def, int_End_description, h0, neg_one_mul],
end

end extra



theorem final_solution_int :
  set_of fn_eq = {(0 : ℤ → ℤ)} ∪ (λ C : ℤ, (λ x : ℤ, 2 * x + C)) '' univ :=
begin
  rw [final_solution_general extra.nat_int_two_torsion_free, ext_iff]; intros f,
  simp only [image_univ, singleton_union, mem_range, mem_image,
             mem_insert_iff, mem_set_of_eq, prod.exists],
  split,

  ---- All functions satisfying the characterization are in the RHS set
  { intros h,
    rcases h with ⟨φ, C, ⟨h, h0⟩, h1⟩,
    rw extra.int_end_sq_eq_one at h,
    cases h with h h,

    -- Solve for f = x ↦ 2x + C
    { right; use C,
      apply funext; intros x,
      change (2 : ℤ) with (1 + 1 : ℤ),
      rw [← h1, pi.add_apply, const_apply, add_left_inj, h, extra.int_End_description,
          add_monoid_hom.add_apply, add_monoid.coe_one, id.def], },
    
    -- Solve for f = 0
    { left,
      rw [h, add_monoid_hom.neg_apply, add_monoid.coe_one, id.def, neg_eq_self ℤ] at h0,
      rw [h0, pi.const_zero, add_zero, h, neg_add_self] at h1,
      rw [← h1, funext_iff]; intros a,
      rw [add_monoid_hom.zero_apply, pi.zero_apply] } },

  ---- All functions on the RHS satisfy the characterization
  { intros h,
    rcases h with h | ⟨C, h⟩,

    -- Check f = 0
    { use [-1, 0]; repeat { split },
      rw [neg_pow_two, one_pow],
      rw [pi.const_zero, add_zero, h, neg_add_self, funext_iff]; intros a,
      rw [add_monoid_hom.zero_apply, pi.zero_apply] },

    -- Check f = x ↦ 2x + C
    { use [1, C]; repeat { split },
      rw funext_iff; intros a,
      rw [← h, pi.add_apply, const_apply, add_left_inj, two_mul,
          add_monoid_hom.add_apply, add_monoid.coe_one, id.def] } },
end

end IMO2019A1
