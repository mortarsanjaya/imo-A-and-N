import IMO2017.A2.A2_basic

/-! # IMO 2017 A2, Case `k = 2` -/

namespace IMOSL
namespace IMO2017A2

open finset
open_locale pointwise

section add_group

variables {G : Type*} [add_group G] [decidable_eq G]

lemma doubleton_sub_self_eq (a b : G) : ({a, b} : finset G) - {a, b} = {0, a - b, b - a} :=
  by rw [insert_eq, union_sub, sub_union, sub_union, singleton_sub_singleton,
    singleton_sub_singleton, singleton_sub_singleton, singleton_sub_singleton,
    sub_self, sub_self, union_assoc, union_comm, ← union_assoc,
    union_right_idem, union_comm, insert_eq, insert_eq]

lemma is_doubleton_sub_self {T : finset G} (h : T.card = 2) :
  ∃ g : G, g ≠ 0 ∧ T - T = {0, g, -g} :=
  exists.elim (card_eq_two.mp h) $ λ a h, exists.elim h $ λ b h,
    ⟨a - b, sub_ne_zero_of_ne h.1, by rw [h.2, doubleton_sub_self_eq, neg_sub]⟩

lemma doubleton_zero_sub_self_eq (g : G) : ({g, 0} : finset G) - {g, 0} = {0, g, -g} :=
  by rw [doubleton_sub_self_eq, zero_sub, sub_zero]

end add_group

variables {R : Type*} [ring R] [decidable_eq R]

lemma doubleton_sub_self_mul (r : R) : let T : finset R := {0, r, -r} in
  ∀ {x y : R}, x ∈ T → y ∈ T → x * y = 0 ∨ x * y = r ^ 2 ∨ x * y = -r ^ 2 :=
λ x y h h0, (mem_insert.mp h).elim (λ h, or.inl $ mul_eq_zero_of_left h y) $
  λ h, (mem_insert.mp h0).imp (mul_eq_zero_of_right x) $
    λ h0, begin
      rw [mem_insert, mem_singleton] at h h0,
      rcases h with rfl | rfl; rcases h0 with rfl | rfl,
      exacts [or.inl (sq y).symm,
              or.inr ((mul_neg x x).trans $ congr_arg _ (sq x).symm),
              or.inr ((neg_mul y y).trans $ congr_arg _ (sq y).symm),
              or.inl ((neg_mul_neg r r).trans (sq r).symm)]
    end

lemma sq_is_sq_add_diff (r : R) : is_sq_add_diff ({0, r, -r} : finset R) (r ^ 2) :=
  let h : (0 : R) ∈ ({0, r, -r} : finset R) := mem_insert_self _ _ in
  ⟨r, 0, 0, 0, mem_insert_of_mem (mem_insert_self r _), h, h, h, eq.symm $
    (add_sub_add_right_eq_sub _ _ _).trans $ sub_eq_self.mpr $ zero_pow (nat.succ_pos 1)⟩

lemma good_one_doubleton_sub_self (r : R) : good (1 : R) ({0, r, -r} : finset R) :=
  λ u v h h0, cast (congr_arg _ (one_mul _).symm) $ (doubleton_sub_self_mul r h h0).elim
    (λ h1, cast (congr_arg _ h1.symm) $ zero_is_sq_add_diff_of_mem $ mem_insert_self 0 _) $
    λ h1, let h2 := sq_is_sq_add_diff r in h1.elim (λ h1, cast (congr_arg _ h1.symm) h2)
      (λ h1, cast (congr_arg _ h1.symm) $ neg_is_sq_add_diff h2)

lemma excellent_two_one : excellent 2 (1 : R) :=
  λ T h, exists.elim (is_doubleton_sub_self h) $
    λ r h, cast (congr_arg _ h.2.symm) $ good_one_doubleton_sub_self r

lemma two_mul_sq_is_sq_add_diff (r : R) :
  is_sq_add_diff ({0, r, -r} : finset R) (2 * r ^ 2) :=
  let h : r ∈ ({0, r, -r} : finset R) := mem_insert_of_mem (mem_insert_self r {-r}),
    h0 : (0 : R) ∈ ({0, r, -r} : finset R) := mem_insert_self 0 {r, -r} in
  ⟨r, r, 0, 0, h, h, h0, h0, (two_mul _).trans $ eq.symm $ sub_eq_self.mpr $
    let h1 : (0 : R) ^ 2 = 0 := zero_pow (nat.succ_pos 1) in
      (congr_arg2 has_add.add h1 h1).trans $ add_zero 0⟩
    
lemma good_two_doubleton_sub_self (r : R) : good (2 : R) ({0, r, -r} : finset R) :=
  λ u v h h0, (doubleton_sub_self_mul r h h0).elim
    (λ h1, cast (congr_arg _ (mul_eq_zero_of_right _ h1).symm) $
      zero_is_sq_add_diff_of_mem $ mem_insert_self 0 _)
    (λ h1, let h2 := two_mul_sq_is_sq_add_diff r in h1.elim
      (λ h1, cast (congr_arg _ $ congr_arg _ h1.symm) h2)
      (λ h1, cast (congr_arg _ $ (neg_mul_eq_mul_neg _ _).trans $ congr_arg _ h1.symm)
        (neg_is_sq_add_diff h2)))

lemma excellent_two_two : excellent 2 (2 : R) :=
  λ T h, exists.elim (is_doubleton_sub_self h) $
    λ r h, cast (congr_arg _ h.2.symm) $ good_two_doubleton_sub_self r



lemma zero_one_sub_self_sq {r : R} (h : r ∈ ({0, 1, -1} : finset R)) :
  r ^ 2 = 0 ∨ r ^ 2 = 1 :=
  (mem_insert.mp h).imp (λ h, (congr_arg _ h).trans $ zero_pow $ nat.succ_pos 1) $
    λ h, (mem_insert.mp h).elim (λ h, (congr_arg _ h).trans $ one_pow 2)
      (λ h, (congr_arg _ $ mem_singleton.mp h).trans neg_one_sq)

lemma zero_one_sub_self_sq_add_sq {r s : R}
  (h : r ∈ ({0, 1, -1} : finset R)) (h0 : s ∈ ({0, 1, -1} : finset R)) :
  r ^ 2 + s ^ 2 = 0 ∨ r ^ 2 + s ^ 2 = 1 ∨ r ^ 2 + s ^ 2 = 2 :=
  let h0 := zero_one_sub_self_sq h0 in (zero_one_sub_self_sq h).elim
    (λ h, h0.elim (λ h0, or.inl $ (congr_arg2 _ h h0).trans $ add_zero 0)
      (λ h0, or.inr $ or.inl $ (congr_arg2 _ h h0).trans $ zero_add 1))
    (λ h, or.inr $ h0.elim (λ h0, or.inl $ (congr_arg2 _ h h0).trans $ add_zero 1)
      (λ h0, or.inr $ congr_arg2 _ h h0))

lemma good_doubleton_zero_one_imp {q : R} (h : good q ({0, 1, -1} : finset R)) :
  q = 0 ∨ (q = 1 ∨ q = -1) ∨ (q = 2 ∨ q = -2) :=
begin
  replace h := is_sq_add_diff_of_good_one_mem h (mem_insert_of_mem $ mem_insert_self 1 _),
  rcases h with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩,

  ---- Split into 9 cases and bash
  rcases zero_one_sub_self_sq_add_sq ha hb with h0 | h0 | h0;
    rcases zero_one_sub_self_sq_add_sq hc hd with h1 | h1 | h1,
  exacts [or.inl (sub_eq_zero_of_eq $ h0.trans h1.symm),
          (or.inr $ (congr_arg2 _ h0 h1).trans $ zero_sub 1).inl.inr,
          (or.inr $ (congr_arg2 _ h0 h1).trans $ zero_sub 2).inr.inr,
          (or.inl $ (congr_arg2 _ h0 h1).trans $ sub_zero 1).inl.inr,
          or.inl (sub_eq_zero_of_eq $ h0.trans h1.symm),
          (or.inr $ (congr_arg2 _ h0 h1).trans $ sub_add_cancel' 1 1).inl.inr,
          (or.inl $ (congr_arg2 _ h0 h1).trans $ sub_zero 2).inr.inr,
          (or.inl $ (congr_arg2 _ h0 h1).trans $ add_sub_cancel 1 1).inl.inr,
          or.inl (sub_eq_zero_of_eq $ h0.trans h1.symm)]
end



/-- Final solution, `k = 2` -/
theorem final_solution_k_eq_2 [nontrivial R] {q : R} :
  excellent 2 q ↔ q = 0 ∨ (q = 1 ∨ q = -1) ∨ (q = 2 ∨ q = -2) :=
  ⟨λ h, good_doubleton_zero_one_imp $ cast (congr_arg _ (doubleton_zero_sub_self_eq 1)) $
    h {1, 0} $ card_doubleton one_ne_zero,
  λ h, h.elim (λ h, cast (congr_arg _ h.symm) $ excellent_any_zero 2) $
    λ h, h.elim
      (λ h, let h0 : excellent 2 (1 : R) := excellent_two_one in
        h.elim (λ h, cast (congr_arg _ h.symm) h0)
          (λ h, cast (congr_arg _ h.symm) $ excellent_neg_of_excellent h0))
      (λ h, let h0 : excellent 2 (2 : R) := excellent_two_two in
        h.elim (λ h, cast (congr_arg _ h.symm) h0)
          (λ h, cast (congr_arg _ h.symm) $ excellent_neg_of_excellent h0))⟩

end IMO2017A2
end IMOSL
