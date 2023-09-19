import data.finset.image data.finset.card logic.lemmas

/-!
# Finite-chain functions

A "finite-chain" function is an injective function `f : α → α` such that `α ∖ f(α)` is finite.
-/

namespace IMOSL
namespace extra

open function

variables {α : Type*}

structure fin_chain_fn (f : α → α) :=
(injective' : injective f)
(range_compl' : finset α)
(range_compl_spec' : (range_compl' : set α) = (set.range f)ᶜ)



namespace fin_chain_fn

section general

variables {f : α → α} (h : fin_chain_fn f)
include h

lemma injective : f.injective :=
  h.injective'

def range_compl : finset α :=
  h.range_compl'

lemma range_compl_spec : (h.range_compl : set α) = (set.range f)ᶜ :=
  h.range_compl_spec'

lemma mem_range_compl_iff {a : α} : a ∈ h.range_compl ↔ a ∉ set.range f :=
  set.ext_iff.mp h.range_compl_spec a

lemma surjective_iff : f.surjective ↔ h.range_compl = ∅ :=
  set.range_iff_surjective.symm.trans $ compl_inj_iff.symm.trans $
    by rw [← h.range_compl_spec, set.compl_univ, finset.coe_eq_empty]

lemma iter_apply_ne_of_mem_range_compl_iter_ne : ∀ {m n : ℕ}, m ≠ n →
  ∀ {a b : α}, a ∈ h.range_compl → b ∈ h.range_compl → (f^[m]) a ≠ (f^[n]) b := 
suffices ∀ {m n}, m < n → ∀ (a b : α), a ∈ h.range_compl → (f^[m]) a ≠ (f^[n]) b,
  from λ m n h0 a b h1 h2, h0.lt_or_lt.elim
    (λ h0, this h0 _ _ h1) (λ h0, (this h0 _ _ h2).symm),
λ m n h0 a b h1 h2, begin
  rcases exists_pos_add_of_lt h0 with ⟨k, h3, rfl⟩,
  rw [iterate_add_apply, (h.injective.iterate m).eq_iff] at h2,
  rw [h2, mem_range_compl_iff, set.mem_range] at h1,
  refine h1 ⟨f^[k.pred] b, _⟩,
  rw [← f.iterate_succ_apply', nat.succ_pred_eq_of_pos h3]
end

lemma iter_injective {a b : α} (h0 : a ∈ h.range_compl) (h1 : b ∈ h.range_compl)
  {m n : ℕ} (h2 : (f^[m]) a = (f^[n]) b) : m = n ∧ a = b :=
suffices m = n, from ⟨this, h.injective.iterate m $ h2.trans $ congr_arg2 _ this.symm rfl⟩,
(eq_or_ne m n).resolve_right $ λ h3, absurd h2 $
  h.iter_apply_ne_of_mem_range_compl_iter_ne h3 h0 h1

lemma iter_eq_iff {a b : α} (h0 : a ∈ h.range_compl) (h1 : b ∈ h.range_compl) {m n : ℕ} :
  (f^[m]) a = (f^[n]) b ↔ m = n ∧ a = b :=
  ⟨h.iter_injective h0 h1, λ h2, congr_arg2 _ h2.1 h2.2⟩

end general



section decidable

variables [decidable_eq α] {f : α → α} (h : fin_chain_fn f)
include h

def exact_iter_range (n : ℕ) : finset α :=
  h.range_compl.image (f^[n])

lemma mem_exact_iter_range_iff' {a : α} {n : ℕ} :
  a ∈ h.exact_iter_range n ↔ ∃ (b : α) (h0 : b ∈ h.range_compl), (f^[n]) b = a :=
  finset.mem_image

lemma mem_exact_iter_range_iff {a : α} {n : ℕ} :
  a ∈ h.exact_iter_range n ↔ ∃ b : α, b ∈ h.range_compl ∧ (f^[n]) b = a :=
  h.mem_exact_iter_range_iff'.trans $ exists_congr $ λ b, exists_prop

lemma exact_iter_range_spec (n : ℕ) :
  (h.exact_iter_range n : set α) = set.range (f^[n]) \ set.range (f^[n + 1]) :=
  set.ext $ λ a, by rw [exact_iter_range, finset.coe_image, h.range_compl_spec,
    iterate_succ, set.range_comp _ f, set.range_diff_image (h.injective.iterate n)]

lemma exact_iter_range_disjoint_of_ne :
  ∀ {m n : ℕ}, m ≠ n → disjoint (h.exact_iter_range m) (h.exact_iter_range n) :=
λ m n h0, finset.disjoint_iff_ne.mpr $ λ c h1 d h2,
  exists.elim (h.mem_exact_iter_range_iff.mp h1) $ λ a h1,
  exists.elim (h.mem_exact_iter_range_iff.mp h2) $ λ b h2,
  h1.2.symm.trans_ne $ (h.iter_apply_ne_of_mem_range_compl_iter_ne h0 h1.1 h2.1).trans_eq h2.2

lemma exact_iter_range_pairwise_disjoint (S : set ℕ) :
  S.pairwise_disjoint h.exact_iter_range :=
  λ m _ n _, h.exact_iter_range_disjoint_of_ne

lemma exact_iter_range_card (n : ℕ) : (h.exact_iter_range n).card = h.range_compl.card :=
  h.range_compl.card_image_of_injective (h.injective.iterate n)



def iter_range_compl (n : ℕ) : finset α :=
  (finset.range n).bUnion h.exact_iter_range

lemma iter_range_compl_eq (n : ℕ) :
  h.iter_range_compl n
    = (finset.range n).disj_Union _ (h.exact_iter_range_pairwise_disjoint _) :=
  ((finset.range n).disj_Union_eq_bUnion _ _).symm

lemma iter_range_compl_zero : h.iter_range_compl 0 = ∅ :=
  rfl

lemma iter_range_compl_succ (n : ℕ) :
  h.iter_range_compl n.succ = h.exact_iter_range n ∪ h.iter_range_compl n :=
  (congr_arg2 _ finset.range_succ rfl).trans finset.bUnion_insert

lemma iter_range_compl_spec (n : ℕ) :
  (h.iter_range_compl n : set α) = (set.range (f^[n]))ᶜ :=
begin
  induction n with n h0,
  exact set.compl_univ.symm.trans (congr_arg _ set.range_id.symm),
  rw [h.iter_range_compl_succ, finset.coe_union, h0, h.exact_iter_range_spec, set.diff_eq,
    set.inter_union_distrib_right, set.union_compl_self, set.univ_inter, ← set.compl_inter],
  refine congr_arg _ (set.inter_eq_left_iff_subset.mpr $ λ x h1, _),
  rw set.mem_range at h1 ⊢, cases h1 with y h1,
  exact ⟨f y, h1⟩
end

lemma mem_iter_range_compl_iff {n : ℕ} {a : α} :
  a ∈ h.iter_range_compl n ↔ a ∉ set.range (f^[n]) :=
  set.ext_iff.mp (h.iter_range_compl_spec n) a

lemma iter_range_compl_subset_succ (n : ℕ) :
  h.iter_range_compl n ⊆ h.iter_range_compl (n + 1) :=
  (finset.subset_union_right _ _).trans_eq (h.iter_range_compl_succ n).symm

lemma iter_range_compl_subset_of_le {m n : ℕ} (h0 : m ≤ n) :
  h.iter_range_compl m ⊆ h.iter_range_compl n :=
  nat.le_induction finset.subset.rfl
    (λ n h0 h1, h1.trans $ h.iter_range_compl_subset_succ n) n h0

lemma iter_range_compl_disjoint_exact_iter_range {m n : ℕ} (h0 : m ≤ n) :
  disjoint (h.exact_iter_range n) (h.iter_range_compl m) :=
  (finset.disjoint_bUnion_right _ _ _).mpr $ λ i h1,
    h.exact_iter_range_disjoint_of_ne ((finset.mem_range.mp h1).trans_le h0).ne.symm

lemma iter_range_compl_card : ∀ n : ℕ, (h.iter_range_compl n).card = n * h.range_compl.card
| 0 := finset.card_empty.trans h.range_compl.card.zero_mul.symm
| (n+1) := (congr_arg finset.card $ h.iter_range_compl_succ n).trans $
    (finset.card_union_eq $ h.iter_range_compl_disjoint_exact_iter_range n.le_refl).trans $
    (congr_arg2 _ (h.exact_iter_range_card n) (iter_range_compl_card n)).trans $
    (nat.add_comm _ _).trans (n.succ_mul _).symm

lemma iter_range_of_range_compl_singleton {a : α} (h0 : h.range_compl = {a}) :
  ∀ n : ℕ, h.iter_range_compl n = (finset.range n).image (λ k, f^[k] a)
| 0 := rfl
| (n+1) := by rw [h.iter_range_compl_succ, exact_iter_range, h0, finset.image_singleton,
    iter_range_of_range_compl_singleton, finset.range_succ, finset.image_insert]; refl


end decidable

end fin_chain_fn

end extra
end IMOSL
