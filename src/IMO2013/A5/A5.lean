import data.finset.basic IMO2013.A5.extra.fin_chain_fn

/-! # IMO 2013 A5 -/

namespace IMOSL
namespace IMO2013A5

open finset
open_locale classical

/- ### Extra lemmas -/

/-- (+4)-induction -/
lemma add_four_induction {P : ℕ → Prop} (h : P 0) (h0 : P 1) (h1 : P 2) (h2 : P 3)
  (h3 : ∀ n, P n → P (n + 4)) : ∀ n, P n
| 0 := h
| 1 := h0
| 2 := h1
| 3 := h2
| (n+4) := h3 n (add_four_induction n)





/- ### Start of the problem -/

def good (f : ℕ → ℕ) := ∀ n : ℕ, f^[3] n = f (n + 1) + 1



lemma good_succ : good nat.succ :=
  λ n, rfl

def answer2 : ℕ → ℕ
| 0 := 1
| 1 := 6
| 2 := 3
| 3 := 0
| (n+4) := answer2 n + 4

lemma good_answer2 : good answer2
| 0 := rfl
| 1 := rfl
| 2 := rfl
| 3 := rfl
| (n+4) := congr_arg (+ 4) (good_answer2 n)





section solution

variables {f : ℕ → ℕ} (h : good f)
include h

lemma iter_four_eq : ∀ n : ℕ, f^[4] n = (f^[4] 0) + n :=
suffices ∀ n : ℕ, f^[4] (n + 1) = (f^[4] n) + 1,
  from λ n, nat.rec_on n rfl $ λ n h0, (this n).trans $ congr_arg nat.succ h0,
λ n, (h $ f (n + 1)).trans $ congr_arg nat.succ $ congr_arg f (h n).symm

lemma good_injective : function.injective f :=
suffices function.injective (f^[3] ∘ f), from this.of_comp,
λ m n h0, nat.add_left_cancel $ (iter_four_eq h m).symm.trans $ h0.trans (iter_four_eq h n)

noncomputable def fin_chain_fn_of_good : extra.fin_chain_fn f :=
{ injective' := good_injective h,
  range_compl' := (range (f^[4] 0)).filter (λ n, n ∉ set.range f),
  range_compl_spec' := set.ext $ λ n, mem_coe.trans $ mem_filter.trans $
    and_iff_right_of_imp $ λ h0, mem_range.mpr $ lt_of_not_le $
    λ h1, h0 ⟨f^[3] (n - (f^[4]) 0), (iter_four_eq h _).trans $ nat.add_sub_of_le h1⟩ }

lemma iter_range_compl_three_subset :
  (fin_chain_fn_of_good h).iter_range_compl 3
    ⊆ insert 0 (insert (f 0).succ $ image nat.succ (fin_chain_fn_of_good h).range_compl) :=
  λ x h0, mem_insert.mpr $ x.eq_zero_or_eq_succ_pred.imp id $
    λ h1, mem_insert.mpr $ (em $ x.pred ∈ set.range f).imp
  (λ h2, h1.trans $ congr_arg nat.succ $ begin
    rw set.mem_range at h2,
    rcases h2 with ⟨n, h2⟩,
    rw ← h2; refine congr_arg f ((eq_or_ne n 0).resolve_right $ λ h3, _),
    rw [h1, ← h2, (fin_chain_fn_of_good h).mem_iter_range_compl_iff] at h0,
    exact h0 ⟨n.pred, (h n.pred).trans (congr_arg nat.succ $ congr_arg f $
      nat.succ_pred_eq_of_pos $ nat.pos_of_ne_zero h3)⟩
  end)
  (λ h2, h1.symm ▸ mem_image_of_mem _ $ (fin_chain_fn_of_good h).mem_range_compl_iff.mpr h2)

lemma card_range_compl_eq_one : (fin_chain_fn_of_good h).range_compl.card = 1 :=
begin
  ---- Reduce to `set.range f ≠ set.univ` (sort of)
  suffices : (fin_chain_fn_of_good h).range_compl ≠ ∅,
  { have h0 := (card_le_of_subset $ iter_range_compl_three_subset h).trans
      ((card_insert_le _ _).trans $ nat.succ_le_succ $ card_insert_le _ _),
    rw [(fin_chain_fn_of_good h).iter_range_compl_card, ← nat.add_succ, nat.succ_mul,
        card_image_of_injective _ nat.succ_injective, add_comm, add_le_add_iff_left,
        mul_le_iff_le_one_right (nat.succ_pos 1), le_iff_eq_or_lt, nat.lt_one_iff] at h0,
    exact h0.resolve_right (λ h0, this $ card_eq_zero.mp h0) },

  ---- Prove that `set.range f ≠ set.univ`
  rw [ne.def, ← (fin_chain_fn_of_good h).surjective_iff],
  intros h0, obtain ⟨a, h1⟩ := h0.iterate 3 0,
  exact (f a.succ).succ_ne_zero ((h a).symm.trans h1)
end

lemma exists_range_compl_eq_singleton : ∃ a : ℕ, (fin_chain_fn_of_good h).range_compl = {a} :=
  card_eq_one.mp $ card_range_compl_eq_one h

lemma iter_four_zero_eq_four : f^[4] 0 = 4 :=
suffices (fin_chain_fn_of_good h).iter_range_compl 4 = range (f^[4] 0),
  by rw [← card_range (f^[4] 0), ← this,
    (fin_chain_fn_of_good h).iter_range_compl_card, card_range_compl_eq_one h, mul_one],
begin
  ext n,
  rw [(fin_chain_fn_of_good h).mem_iter_range_compl_iff, mem_range,
      not_iff_comm, not_lt, set.mem_range, le_iff_exists_add],
  refine exists_congr (λ a, _),
  rw [eq_comm, iter_four_eq h a]
end

lemma map_add_four (n : ℕ) : f (n + 4) = f n + 4 :=
  iter_four_zero_eq_four h ▸
    by rw [add_comm, ← iter_four_eq h, add_comm, ← iter_four_eq h]; refl



section

variables {a : ℕ} (h0 : (fin_chain_fn_of_good h).range_compl = {a})
include h0

lemma iter_range_three_a_finset_eq :
  ({f (f a), f a, a} : finset ℕ) = {0, f 0 + 1, a + 1} :=
begin
  have h1 := eq_of_subset_of_card_le (iter_range_compl_three_subset h) _,
  rwa [(fin_chain_fn_of_good h).iter_range_of_range_compl_singleton h0,
    h0, image_singleton, range_succ, range_succ, range_one,
    image_insert, image_insert, image_singleton] at h1,
  
  rw [(fin_chain_fn_of_good h).iter_range_compl_card, card_range_compl_eq_one h, mul_one],
  refine (card_insert_le _ _).trans (nat.succ_le_succ $
    (card_insert_le _ _).trans $ nat.succ_le_succ $ card_image_le.trans _),
  rw [h0, card_singleton]
end

/-- Multiset variants are easier to work with in case division -/
lemma iter_range_three_a_multiset_eq :
  ({f (f a), f a, a} : multiset ℕ) = {0, f 0 + 1, a + 1} :=
begin
  have h1 := congr_arg val (iter_range_three_a_finset_eq h h0),
  rw ext_iff at h0,
  simp_rw [mem_singleton, (fin_chain_fn_of_good h).mem_range_compl_iff] at h0,
  have h2 : f a = a → false := λ h2, (h0 (f a)).mpr h2 ⟨a, rfl⟩,
  rwa [insert_val_of_not_mem (λ h3, (mem_insert.mp h3).elim (λ h3, h2 $ good_injective h h3)
         (λ h3, (h0 (f $ f a)).mpr (mem_singleton.mp h3) ⟨f a, rfl⟩)),
       insert_val_of_not_mem (λ h3, h2 $ mem_singleton.mp h3),
       insert_val_of_not_mem (λ h3, (mem_insert.mp h3).elim (f 0).succ_ne_zero.symm
         (λ h3, absurd (mem_singleton.mp h3) a.succ_ne_zero.symm)),
       insert_val_of_not_mem (λ h3, (h0 (f 0)).mpr
        (nat.succ_injective $ mem_singleton.mp h3) ⟨0, rfl⟩)] at h1
end

lemma iter_range_three_cases :
  f a = a + 1 ∧ (a = f 0 + 1 ∧ f (f 0 + 2) = 0 ∨ a = 0 ∧ f 1 = 2) :=
begin
  have h1 := iter_range_three_a_multiset_eq h h0,
  iterate 4 { rw multiset.insert_eq_cons at h1 },
  have h2 := iff_of_eq (congr_arg2 has_mem.mem (rfl : a + 1 = a + 1) h1),
  iterate 4 { rw multiset.mem_cons at h2 },
  replace h2 := h2.mpr (or.inr $ mem_singleton_self _).inr,
  rw [multiset.mem_singleton, or_iff_left a.succ_ne_self] at h2,
  ---- Get rid of the case `a + 1 = f(f(a))`
  cases h2 with h2 h2,
  exact absurd (h a) ((congr_arg f h2.symm).trans_ne (f a.succ).succ_ne_self.symm),
  ---- Now the main cases
  refine ⟨h2.symm, _⟩,
  iterate 4 { rw ← multiset.singleton_add at h1 },
  rw [← h2, ← add_assoc, ← add_assoc, add_right_comm, add_left_inj,
      multiset.singleton_add, multiset.singleton_add, multiset.cons_eq_cons] at h1,
  revert h1; refine or.imp (λ h1, _) (λ h1, _),
  -- Case 1: `a = f(0) + 1` and `f(a + 1) = 0`,
  { cases h1 with h1 h2,
    rw multiset.singleton_inj at h2,
    exact ⟨h2, (congr_arg f $ congr_arg nat.succ h2.symm).trans h1⟩ },
  -- Case 2: `a = 0` and `f(a + 1) = f(0) + 1`
  { rcases h1 with ⟨h1, S, h2, h3⟩,
    rw multiset.singleton_eq_cons_iff at h2,
    rcases h2 with ⟨rfl, rfl⟩,
    rw [multiset.cons_zero, ← h2, zero_add, multiset.singleton_inj] at h3,
    exact ⟨rfl, h3.symm⟩ }
end

end



lemma case1 (h0 : f (f 0 + 1) = f 0 + 2) (h1 : f (f 0 + 2) = 0) : f = answer2 :=
begin
  have h2 := h (f 0 + 1),
  rw [f.iterate_succ_apply, h0, f.iterate_succ_apply, h1, f.iterate_one, zero_add] at h2,
  rw h2 at h0 h1,
  have h3 := h 3,
  rwa [f.iterate_succ_apply, h1, f.iterate_succ_apply, h2,
      ← zero_add (3 + 1), map_add_four h, h2] at h3,
  exact funext (add_four_induction h2 h3 h0 h1 $
    λ n h4, (map_add_four h n).trans $ congr_arg (+ 4) h4)
end

lemma case2 (h0 : f 0 = 1) (h1 : f 1 = 2) : f = nat.succ :=
begin
  have h2 := h 0,
  rw [f.iterate_succ_apply, h0, f.iterate_succ_apply, h1, f.iterate_one] at h2,
  have h3 := h 1,
  rw [f.iterate_succ_apply, h1, f.iterate_succ_apply, h2, f.iterate_one] at h3,
  exact funext (add_four_induction h0 h1 h2 h3 $
    λ n h4, (map_add_four h n).trans $ congr_arg (+ 4) h4)
end

end solution





/-- Final solution -/
theorem final_solution {f : ℕ → ℕ} : good f ↔ f = nat.succ ∨ f = answer2 :=
  ⟨λ h, exists.elim (exists_range_compl_eq_singleton h) $ λ a h0,
    let h1 := iter_range_three_cases h h0 in h1.2.symm.imp
      (λ h2, case2 h (by rw h2.1 at h1; exact h1.1) h2.2)
      (λ h2, case1 h (by rw h2.1 at h1; exact h1.1) h2.2),
  λ h, h.elim (λ h, h.symm ▸ good_succ) (λ h, h.symm ▸ good_answer2)⟩

end IMO2013A5
end IMOSL
