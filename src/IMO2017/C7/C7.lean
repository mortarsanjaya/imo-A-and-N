import data.nat.nth

/-! # IMO 2017 C7 -/

namespace IMOSL
namespace IMO2017C7

open finset function

/-! Extra lemmas -/
section extra_lemmas

lemma strict_mono_eq_at_large_comm {f g : ℕ → ℕ}
  (hf : strict_mono f) (hg : strict_mono g)
  (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = g n) (h0 : f ∘ g = g ∘ f) : f = g :=
begin
  cases h with N h,
  ext n; have h1 := n.zero_le; revert h1 n,
  refine nat.decreasing_induction (λ k h1 n h2, _) N.zero_le h,
  rw [le_iff_lt_or_eq, ← nat.add_one_le_iff] at h2,
  rcases h2 with h2 | rfl,
  exact h1 n h2,
  cases eq_or_lt_of_le (hf.id_le k) with h3 h3,
  cases eq_or_lt_of_le (hg.id_le k) with h4 h4,
  { rw [← h3, ← h4] },
  { exact hg.injective ((congr_fun h0.symm k).trans $ h1 (g k) h4) },
  { exact hf.injective ((h1 (f k) h3).trans $ congr_fun h0.symm k) }
end

lemma count_true : ∀ n : ℕ, nat.count (λ _, true) n = n
| 0 := rfl
| (n+1) := (nat.count_succ _ n).trans $ 
    congr_arg2 has_add.add (count_true n) (if_true 1 0)

lemma nth_true : nat.nth (λ _, true) = id :=
  funext $ λ n, (congr_arg (nat.nth $ λ _, true) (count_true n).symm).trans $
    nat.nth_count trivial

section classical
open_locale classical

lemma count_prop_inj {p q : ℕ → Prop}
  (h : ∀ n : ℕ, nat.count p n = nat.count q n) : p = q :=
  funext $ λ n, by rw [← @nat.count_succ_eq_succ_count_iff p, h,
    h, nat.count_succ_eq_succ_count_iff]

lemma nth_prop_inj {p q : ℕ → Prop}
  (hp : (set_of p).infinite) (hq : (set_of q).infinite) :
  nat.nth p = nat.nth q ↔ p = q :=
  ⟨λ h, count_prop_inj $ λ n, galois_connection.l_unique
    (nat.gc_count_nth hp) (nat.gc_count_nth hq) (congr_fun h),
  congr_arg nat.nth⟩

end classical

lemma nat_finset_infinite_compl (X : finset ℕ) : {n : ℕ | n ∉ X}.infinite :=
  by have h := (X : set ℕ).to_finite.infinite_compl; rwa set.compl_def at h

end extra_lemmas







/-! `ℕset` and its properties -/

/-- `finset ℕ` but with the special multiplication operation -/
def ℕset := finset ℕ



namespace ℕset

instance : has_emptyc ℕset := finset.has_emptyc
instance : has_mem ℕ ℕset := finset.has_mem
instance : has_union ℕset := finset.has_union
instance : has_inter ℕset := finset.has_inter
instance : has_coe_t ℕset (set ℕ) := finset.set.has_coe_t

instance : has_one ℕset := ⟨∅⟩
instance : inhabited ℕset := ⟨∅⟩

lemma one_eq_empty : (1 : ℕset) = ∅ := rfl



/-- `f_X(n)` is the `n`th element not in `X`, indexed from `0`. -/
noncomputable def nth_notin (X : ℕset) : function.End ℕ := nat.nth (λ n, n ∉ X)

/-- `nth_notin` is an embedding to `End(ℕ)`; we see later that it is injective. -/
noncomputable instance : has_coe_t ℕset (function.End ℕ) := ⟨nth_notin⟩

lemma coe_fun_eq_nth_notin (X : ℕset) : (X : function.End ℕ) = nth_notin X := rfl

lemma coe_fun_one : ((1 : ℕset) : function.End ℕ) = id :=
  (congr_arg nat.nth $ funext $ λ n, eq_true_iff.mpr (not_mem_empty n : n ∉ ∅)).trans nth_true

private lemma range_coe_fun_eq_compl (X : ℕset) : set.range (X : function.End ℕ) = Xᶜ :=
  set.ext $ λ n, ⟨λ h, exists.elim h $ λ y h0, by rw ← h0;
      exact nat.nth_mem_of_infinite (nat_finset_infinite_compl X) y,
    λ h, ⟨nat.count (λ n, n ∉ X) n, nat.nth_count h⟩⟩

private lemma range_coe_fun_eq_univ_diff (X : ℕset) :
  set.range (X : function.End ℕ) = set.univ \ X :=
  (range_coe_fun_eq_compl X).trans (set.compl_eq_univ_diff ↑X)

private lemma coe_fun_inj {X Y : ℕset} : (X : function.End ℕ) = Y ↔ X = Y :=
  (nth_prop_inj (nat_finset_infinite_compl X) (nat_finset_infinite_compl Y)).trans
  ⟨λ h, ext $ λ n, not_iff_not.mp $ iff_of_eq $ congr_fun h n,
    λ h, funext $ λ n, congr_arg not $ congr_arg (has_mem.mem n) h⟩

private lemma coe_fun_strict_mono (X : ℕset) : strict_mono (X : function.End ℕ) :=
  nat.nth_strict_mono (nat_finset_infinite_compl X)

private lemma coe_fun_map_inj (X : ℕset) : injective (X : function.End ℕ) :=
  strict_mono.injective (coe_fun_strict_mono X)



/-- Plain supremum of an `ℕset` -/
def sup (X : ℕset) := X.sup id

private lemma count_notin_large {X : ℕset} {n : ℕ} (h : X.sup < n) :
  nat.count (λ x, x ∉ X) (n + X.card) = n :=
begin
  have h0 := congr_arg card (filter_union_filter_neg_eq (λ x, x ∈ X) (range (n + X.card))),
  rw [card_range, card_union_eq, ← nat.count_eq_card_filter_range,
      ← nat.count_eq_card_filter_range, nat.count_eq_card_fintype] at h0,
  work_on_goal 2 { rw disjoint_iff_inter_eq_empty, exact filter_inter_filter_neg_eq _ _ _ },
  rw [← add_left_inj X.card, add_comm],
  revert h0; refine eq.trans (congr_arg2 has_add.add _ rfl),
  suffices : ∀ k : ℕ, k ∈ X ↔ (k < n + X.card ∧ k ∈ X),
    refine (fintype.subtype_card X this).symm.trans _,
    convert rfl using 2,
  refine λ k, iff_and_self.mpr (λ h0, lt_of_le_of_lt (le_sup h0) (lt_trans h _)),
  rw [lt_add_iff_pos_right, pos_iff_ne_zero, ne.def, card_eq_zero],
  exact ne_empty_of_mem h0
end

private lemma coe_fun_map_large {X : ℕset} {n : ℕ} (h : X.sup < n) :
  (X : function.End ℕ) n = n + X.card :=
begin
  have h0 := nat_finset_infinite_compl X,
  rw [coe_fun_eq_nth_notin, nth_notin, eq_comm, eq_iff_le_not_lt]; split,
  rw [← nat.count_le_iff_le_nth h0, count_notin_large h],
  rw [← nat.succ_le_iff, ← nat.count_le_iff_le_nth h0, nat.count_succ, count_notin_large h,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero, ← ne.def, ite_ne_right_iff, and_comm],
  refine ⟨one_ne_zero, λ h1, _⟩,
  replace h1 : id (n + X.card) ≤ X.sup := le_sup h1,
  rw [id.def, ← not_lt] at h1,
  exact h1 (lt_of_lt_of_le h le_self_add)
end



/-- Multiplication based on `nth_notin` -/
noncomputable def mul (X Y : ℕset) := X ∪ image (X : function.End ℕ) Y

noncomputable instance : has_mul ℕset := ⟨mul⟩

lemma mul_def (X Y : ℕset) : X * Y = X ∪ image (X : function.End ℕ) Y := rfl

lemma mul_one (X : ℕset) : X * 1 = X :=
  union_empty X

lemma one_mul (X : ℕset) : 1 * X = X :=
  (empty_union _).trans $ (congr_arg2 image coe_fun_one rfl).trans image_id

lemma card_mul (X Y : ℕset) : (X * Y).card = X.card + Y.card :=
begin
  rw [mul_def, card_disjoint_union, card_image_of_injective Y (coe_fun_map_inj X)],
  rw disjoint_right; intros a h1 h0,
  rw ← mem_coe at h1,
  replace h1 : a ∈ set.range (X : function.End ℕ) := coe_image_subset_range h1,
  rw [range_coe_fun_eq_compl, set.mem_compl_iff, finset.mem_coe] at h1,
  exact h1 h0
end

lemma range_mul (X Y : ℕset) : set.range ((X * Y : ℕset) : function.End ℕ) =
  set.range ((X : function.End ℕ) ∘ (Y : function.End ℕ)) :=
  by rw [range_coe_fun_eq_compl, set.range_comp (X : function.End ℕ),
    range_coe_fun_eq_univ_diff, set.image_diff (coe_fun_map_inj X),
    set.image_univ, range_coe_fun_eq_univ_diff, set.diff_diff,
    ← set.compl_eq_univ_diff, compl_inj_iff, mul_def, coe_union, coe_image]

/-- Lemma 1 in the official solution. The lemma implies `mul_assoc`.
  Thus `ℕset` is a monoid, and the coercion to `function.End ℕ` is a monoid homomorphism. -/
lemma coe_fun_mul (X Y : ℕset) : ((X * Y : ℕset) : function.End ℕ) = X * Y :=
  (well_founded.eq_strict_mono_iff_eq_range is_well_founded.wf (coe_fun_strict_mono _) $
    (coe_fun_strict_mono X).comp (coe_fun_strict_mono Y)).mp $ range_mul X Y

lemma mul_assoc (X Y Z : ℕset) : X * Y * Z = X * (Y * Z) :=
  coe_fun_inj.mp $ by iterate 4 { rw coe_fun_mul }; rw mul_assoc

noncomputable instance : monoid ℕset :=
{ one := has_one.one,
  mul := has_mul.mul,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one }



/-- Cardinality as a monoid homomorphism -/
def card_hom : ℕset →* multiplicative ℕ :=
  ⟨additive.to_mul ∘ finset.card, congr_arg additive.to_mul card_empty, card_mul⟩

lemma card_pow : ∀ (X : ℕset) (k : ℕ), (X ^ k).card = k * X.card :=
  card_hom.map_pow



/-- Lemma 2 in the official solution. If `|X| = |Y|` and `XY = YX`, then `X = Y`. -/
lemma commute_eq_card_imp_eq {X Y : ℕset}
  (h : X.card = Y.card) (h0 : X * Y = Y * X) : X = Y :=
begin
  rw ← coe_fun_inj at h0 ⊢,
  rw [coe_fun_mul, coe_fun_mul] at h0,
  refine strict_mono_eq_at_large_comm (coe_fun_strict_mono X) (coe_fun_strict_mono Y)
    ⟨(max X.sup Y.sup).succ, λ n h1, _⟩ h0,
  rw [nat.succ_le_iff, max_lt_iff] at h1,
  cases h1 with h1 h2,
  rw [coe_fun_map_large h1, coe_fun_map_large h2, h]
end

/-- The main problem to be solved. The `final_solution` theorem will be its alias. -/
lemma commute_pow_card_eq {X Y : ℕset} (h : X * Y = Y * X) : X ^ Y.card = Y ^ X.card :=
  commute_eq_card_imp_eq
    ((card_pow X Y.card).trans $ (mul_comm Y.card X.card).trans (card_pow Y X.card).symm)
    (commute.pow_pow h Y.card X.card)

end ℕset



/-- Final solution (alias of `commute_pow_card_eq`) -/
alias ℕset.commute_pow_card_eq ← final_solution

end IMO2017C7
end IMOSL
