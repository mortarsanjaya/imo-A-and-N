import data.nat.nth

/-! # IMO 2017 C7 -/

namespace IMOSL
namespace IMO2017C7

open finset function

/- ### Extra lemmas -/

section extra_lemmas

/-- Decreasing induction on `ℕ` up to `0` -/
lemma nat_decreasing_induction_zero {P : ℕ → Prop} (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → P n)
  (h0 : ∀ n, (∀ k, n < k → P k) → P n) : ∀ n : ℕ, P n :=
suffices ∀ n : ℕ, 0 ≤ n → P n, from λ n, this n n.zero_le,
exists.elim h $ λ N h, nat.decreasing_induction
  (λ t h1 n h2, h2.lt_or_eq.elim (h1 n) $ λ h2, h2 ▸ h0 t h1) N.zero_le h

/-- For some reason, this lemma is nowhere to be found in mathlib. -/
lemma function_End_pow_eq_iterate {α : Type*} (f : function.End α) : ∀ k : ℕ, f ^ k = (f^[k])
| 0 := rfl
| (k+1) := eq.symm $ (f.iterate_succ' k).trans $ function_End_pow_eq_iterate k ▸ rfl

lemma strict_mono_eq_at_large_comm {f g : ℕ → ℕ} (hf : strict_mono f) (hg : strict_mono g)
  (h : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f n = g n) (h0 : f ∘ g = g ∘ f) : f = g :=
  funext $ nat_decreasing_induction_zero h $
    λ n h, (hf.id_le n).lt_or_eq.elim
      (λ h1, hf.injective $ (h (f n) h1).trans $ congr_fun h0.symm n) $
      λ h1, (hg.id_le n).eq_or_lt.elim h1.symm.trans
        (λ h2, hg.injective $ (congr_fun h0.symm n).trans $ h (g n) h2)

lemma strict_mono_iterate_comm_at_large {f g : ℕ → ℕ} {N : ℕ}
  (hf : strict_mono f) (h : ∀ n : ℕ, N < n → f (g n) = g (f n)) :
  ∀ k n : ℕ, N < n → (f^[k]) (g n) = g (f^[k] n)
| 0 n _ := rfl
| (k+1) n h0 := (iterate_succ_apply f k (g n)).trans $ (congr_arg _ $ h n h0).trans $
    (strict_mono_iterate_comm_at_large k (f n) $ h0.trans_le $ hf.id_le n).trans $
      congr_arg g (iterate_succ_apply f k n).symm

lemma strict_mono_comm_of_comm_at_large_of_iter_comm {f g : ℕ → ℕ} 
  (hf : strict_mono f) {k : ℕ} (h : 0 < k) (h0 : (f^[k]) ∘ g = g ∘ (f^[k]))
  (h1 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → f (g n) = g (f n)) : f ∘ g = g ∘ f :=
funext $ nat_decreasing_induction_zero h1 $ λ n h1, (hf.id_le n).eq_or_lt.elim
---- Case 1: `f(n) = n`
(λ h2, begin
  rw [comp_app, comp_app, ← h2],
  refine nat.le_antisymm _ (hf.id_le (g n)),
  have h3 := congr_fun h0 n,
  rw [comp_app, comp_app, iterate_fixed h2.symm] at h3,
  nth_rewrite 1 ← h3,
  rw [← nat.sub_add_cancel h, iterate_succ],
  exact (hf.iterate $ k - 1).id_le (f (g n))
end)
---- Case 2: `f(n) > n`
(λ h2, begin
  have h3 := congr_fun h0 n,
  rw [← nat.sub_add_cancel h, iterate_succ] at h3,
  exact (hf.iterate $ k - 1).injective 
    (h3.trans (strict_mono_iterate_comm_at_large hf h1 (k - 1) (f n) h2).symm)
end)

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
  (X : set ℕ).compl_def ▸ (X : set ℕ).to_finite.infinite_compl
  -- by have h := (X : set ℕ).to_finite.infinite_compl; rwa set.compl_def at h

end extra_lemmas





/- ### `ℕset` and its properties -/

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

lemma range_coe_fun_eq_compl (X : ℕset) : set.range (X : function.End ℕ) = Xᶜ :=
  set.ext $ λ n, ⟨λ h, exists.elim h $ λ y h0, by rw ← h0;
      exact nat.nth_mem_of_infinite (nat_finset_infinite_compl X) y,
    λ h, ⟨nat.count (λ n, n ∉ X) n, nat.nth_count h⟩⟩

lemma range_coe_fun_eq_univ_diff (X : ℕset) :
  set.range (X : function.End ℕ) = set.univ \ X :=
  (range_coe_fun_eq_compl X).trans (set.compl_eq_univ_diff ↑X)

lemma coe_fun_inj {X Y : ℕset} : (X : function.End ℕ) = Y ↔ X = Y :=
  (nth_prop_inj (nat_finset_infinite_compl X) (nat_finset_infinite_compl Y)).trans
  ⟨λ h, ext $ λ n, not_iff_not.mp $ iff_of_eq $ congr_fun h n,
    λ h, funext $ λ n, congr_arg not $ congr_arg (has_mem.mem n) h⟩

lemma coe_fun_strict_mono (X : ℕset) : strict_mono (X : function.End ℕ) :=
  nat.nth_strict_mono (nat_finset_infinite_compl X)

lemma coe_fun_map_inj (X : ℕset) : injective (X : function.End ℕ) :=
  strict_mono.injective (coe_fun_strict_mono X)



/-- Plain supremum of an `ℕset` -/
def sup (X : ℕset) := X.sup id

lemma count_notin_large {X : ℕset} {n : ℕ} (h : X.sup < n) :
  nat.count (λ x, x ∉ X) (n + X.card) = n :=
begin
  rw [← add_right_inj (filter (λ (x : ℕ), x ∈ X) (range (n + card X))).card,
      nat.count_eq_card_filter_range, ← card_union_eq],
  work_on_goal 2 { rw disjoint_iff_inter_eq_empty, exact filter_inter_filter_neg_eq _ _ _ },
  rw [filter_union_filter_neg_eq, card_range, add_comm, add_left_inj],
  refine congr_arg card (ext $ λ x, _),
  rw [mem_filter, iff_and_self, mem_range],
  exact λ h0, (le_sup h0).trans_lt (h.trans $ nat.lt_add_of_pos_left $ card_pos.mpr ⟨x, h0⟩)
end

lemma coe_fun_map_large {X : ℕset} {n : ℕ} (h : X.sup < n) :
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
  exact h1 (h.trans_le le_self_add)
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

lemma coe_fun_mul_apply (X Y : ℕset) (n : ℕ) :
  ((X * Y : ℕset) : function.End ℕ) n = (X : function.End ℕ) ((Y : function.End ℕ) n) :=
    congr_fun (coe_fun_mul X Y) n

lemma mul_assoc (X Y Z : ℕset) : X * Y * Z = X * (Y * Z) :=
  coe_fun_inj.mp $ by iterate 4 { rw coe_fun_mul }; rw mul_assoc

noncomputable instance : monoid ℕset :=
{ one := has_one.one,
  mul := has_mul.mul,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one }

lemma mul_left_cancel {X Y Z : ℕset} (h : X * Y = X * Z) : Y = Z :=
  coe_fun_inj.mp $ funext $ λ n, coe_fun_map_inj X $
    by rw [← coe_fun_mul_apply, ← coe_fun_mul_apply, h]

noncomputable instance : left_cancel_monoid ℕset := 
{ mul_left_cancel := λ X Y Z, mul_left_cancel
  .. ℕset.monoid }



/-- Cardinality as a monoid homomorphism -/
def card_hom : ℕset →* multiplicative ℕ :=
  ⟨additive.to_mul ∘ finset.card, congr_arg additive.to_mul card_empty, card_mul⟩

lemma card_pow : ∀ (X : ℕset) (k : ℕ), (X ^ k).card = k * X.card :=
  card_hom.map_pow

lemma card_eq_zero_iff {X : ℕset} : X.card = 0 ↔ X = 1 :=
  finset.card_eq_zero

lemma exists_le_imp_congr_fun_of_card_eq {X Y : ℕset} (h : X.card = Y.card) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (X : function.End ℕ) n = (Y : function.End ℕ) n :=
  ⟨(max X.sup Y.sup).succ, λ n h0, by rw [nat.succ_le_iff, max_lt_iff] at h0;
    rw [coe_fun_map_large h0.1, coe_fun_map_large h0.2, h]⟩

/-- Coercion to `function.End ℕ` as a monoid homomorphism -/
noncomputable def coe_t_hom : ℕset →* (function.End ℕ) :=
  ⟨λ X, X, coe_fun_one, coe_fun_mul⟩

lemma coe_fun_pow : ∀ (X : ℕset) (k : ℕ), ((X ^ k : ℕset) : function.End ℕ) = X ^ k :=
  coe_t_hom.map_pow





/- ### Main results -/

/-- If `|X| = |Y|` and `XY = YX`, then `X = Y`. (Lemma 2 in the official solution) -/
lemma commute_eq_card_imp_eq {X Y : ℕset} (h : X.card = Y.card) (h0 : X * Y = Y * X) :
  X = Y :=
begin
  rw ← coe_fun_inj at h0 ⊢,
  rw [coe_fun_mul, coe_fun_mul] at h0,
  exact strict_mono_eq_at_large_comm (coe_fun_strict_mono X)
    (coe_fun_strict_mono Y) (exists_le_imp_congr_fun_of_card_eq h) h0
end

/-- If `XY = YX`, then `X^{|Y|} = Y^{|X|}`. -/
lemma commute_imp_pow_card_eq {X Y : ℕset} (h : X * Y = Y * X) : X ^ Y.card = Y ^ X.card :=
  commute_eq_card_imp_eq
    ((card_pow X Y.card).trans $ (mul_comm Y.card X.card).trans (card_pow Y X.card).symm)
    (commute.pow_pow h Y.card X.card)

/-- Given `k > 0` and `X Y : ℕset`, if `X^k Y = Y X^k`, then `XY = YX`. -/
lemma commute_of_pow_commute' {X Y : ℕset} {k : ℕ} (h : 0 < k) (h0 : X ^ k * Y = Y * X ^ k) :
  X * Y = Y * X :=
begin
  rw [← coe_fun_inj, coe_fun_mul, coe_fun_mul] at h0 ⊢,
  rw coe_fun_pow at h0,
  refine strict_mono_comm_of_comm_at_large_of_iter_comm
    (coe_fun_strict_mono X) h (by rwa ← function_End_pow_eq_iterate) _,
  have h1 : (X * Y).card = (Y * X).card := by rw [card_mul, card_mul, add_comm],
  have h2 := exists_le_imp_congr_fun_of_card_eq h1,
  rwa [coe_fun_mul, coe_fun_mul] at h2
end

/-- Given `k, m > 0` and `X Y : ℕset`, if `X^k Y^m = Y^m X^k`, then `XY = YX`. -/
lemma commute_of_pow_commute {X Y : ℕset} {k m : ℕ} (h : 0 < k) (h0 : 0 < m)
  (h1 : X ^ k * Y ^ m = Y ^ m * X ^ k) : X * Y = Y * X :=
  commute_of_pow_commute' h $ (commute_of_pow_commute' h0 h1.symm).symm

/-- If `X^{|Y|} = Y^{|X|}`, then `XY = YX`. -/
lemma pow_card_eq_imp_commute {X Y : ℕset} (h : X ^ Y.card = Y ^ X.card) : X * Y = Y * X :=
  X.card.eq_zero_or_pos.elim (λ h0, by rw [card_eq_zero_iff.mp h0, one_mul, mul_one]) $
  λ h0, Y.card.eq_zero_or_pos.elim (λ h1, by rw [card_eq_zero_iff.mp h1, one_mul, mul_one]) $
  λ h1, (commute_of_pow_commute h0 h1 $ congr_arg2 has_mul.mul h.symm h).symm

/-- `XY = YX` if and only if `X^{|Y|} = Y^{|X|}`. -/
lemma commute_iff_pow_card_eq {X Y : ℕset} : X * Y = Y * X ↔ X ^ Y.card = Y ^ X.card :=
  ⟨commute_imp_pow_card_eq, pow_card_eq_imp_commute⟩

end ℕset





/-- Final solution (alias of `commute_imp_pow_card_eq`) -/
alias ℕset.commute_imp_pow_card_eq ← final_solution

/-- Final solution, extra version (alias of `pow_card_eq_imp_commute`) -/
alias ℕset.pow_card_eq_imp_commute ← final_solution_extra

end IMO2017C7
end IMOSL
