import data.nat.nth data.finset.basic

/-! # IMO 2017 C7 -/

open finset function

namespace IMOSL
namespace IMO2017C7

noncomputable def nth_notin (X : finset ℕ) := nat.nth (λ n, n ∉ X)
noncomputable def cup_mul (X Y : finset ℕ) := X ∪ image (nth_notin X) Y
noncomputable def cup_pow (X : finset ℕ) (k : ℕ) := nat.iterate (λ Y, cup_mul X Y) k ∅
local infix ` ** `:80 := cup_mul
local infix ` ^^ `:100 := cup_pow



section prop_lemmas

private lemma count_true : nat.count (λ _, true) = id :=
begin
 ext n; induction n with n n_ih,
 rw [nat.count_zero, id.def],
 rw [nat.count_succ, n_ih, if_true, id.def, id.def]
end

private lemma nth_true : nat.nth (λ _, true) = id :=
begin
  ext n; have h := nat.nth_count (λ _, true) (trivial : (λ _, true) n),
  rwa count_true at h
end

variables {p q : ℕ → Prop} [decidable_pred p] [decidable_pred q]

private lemma count_prop_inj (h : ∀ n : ℕ, nat.count p n = nat.count q n) : p = q :=
  by ext n; rw [← @nat.count_succ_eq_succ_count_iff p, h, h, nat.count_succ_eq_succ_count_iff]

private lemma nth_prop_inj (hp : (set_of p).infinite) (hq : (set_of q).infinite) :
  nat.nth p = nat.nth q ↔ p = q :=
begin
  symmetry; split,
  intros h; rw h,
  intros h; refine count_prop_inj (λ n, _),
  exact galois_connection.l_unique (nat.count_nth_gc _ hp) (nat.count_nth_gc _ hq) (λ b, by rw h)
end



end prop_lemmas



section finset_lemmas

variables (X Y : finset ℕ)

private lemma nat_finset_infinite_compl : {n : ℕ | n ∉ X}.infinite :=
begin
  have h := set.finite.infinite_compl ((X : set ℕ).to_finite),
  rwa set.compl_def at h
end

private lemma range_nth_notin_eq_compl : set.range (nth_notin X) = Xᶜ :=
begin
  ext n; rw [set.mem_range, set.mem_compl_eq, mem_coe],
  refine ⟨_, (λ h, ⟨nat.count (λ n, n ∉ X) n, _⟩)⟩,
  rintros ⟨y, rfl⟩,
  exact nat.nth_mem_of_infinite (λ n, n ∉ X) (nat_finset_infinite_compl X) y,
  exact nat.nth_count (λ (n : ℕ), n ∉ X) h
end

private lemma range_nth_notin_eq_univ_diff : set.range (nth_notin X) = set.univ \ X :=
  by rw [range_nth_notin_eq_compl, set.compl_eq_univ_diff]

private lemma nth_notin_inj : nth_notin X = nth_notin Y ↔ X = Y :=
begin
  unfold nth_notin,
  rw nth_prop_inj (nat_finset_infinite_compl X) (nat_finset_infinite_compl Y),
  symmetry; split,
  intros h; rw h,
  intros h; ext n,
  replace h := congr_fun h n,
  simp only [eq_iff_iff] at h,
  rwa [← not_iff_not, ← mem_coe, set.not_not_mem, ← mem_coe, set.not_not_mem] at h
end

private lemma nth_notin_strict_mono : strict_mono (nth_notin X) :=
  nat.nth_strict_mono _ (nat_finset_infinite_compl X)

private lemma nth_notin_fn_inj : injective (nth_notin X) :=
  strict_mono.injective (nth_notin_strict_mono X)

lemma nth_notin_empty : nth_notin ∅ = id :=
  by simp [nth_notin, nth_true]

/-
private lemma range_nth_notin_inj : set.range (nth_notin X) = set.range (nth_notin Y) ↔ X = Y :=
  by let h := nth_notin_strict_mono;
    rw [well_founded.eq_strict_mono_iff_eq_range is_well_order.wf (h X) (h Y), nth_notin_inj]
-/

end finset_lemmas



section cup_mul_lemmas

lemma cup_mul_empty (X : finset ℕ) : X ** ∅ = X :=
  by rw [cup_mul, image_empty, union_empty]
  
lemma empty_cup_mul (X : finset ℕ) : ∅ ** X = X :=
  by rw [cup_mul, empty_union, nth_notin_empty, image_id]

/- For any `X Y : finset ℕ`, `|X ** Y| = |X| + |Y|`. -/
lemma cup_mul_card (X Y : finset ℕ) : (X ** Y).card = X.card + Y.card :=
begin
  rw [cup_mul, card_disjoint_union, card_image_of_injective Y (nth_notin_fn_inj X)],
  rw disjoint_right; intros a h1 h0,
  rw ← mem_coe at h1,
  replace h1 : a ∈ set.range (nth_notin X) := coe_image_subset_range h1,
  rw [range_nth_notin_eq_compl, set.mem_compl_eq, finset.mem_coe] at h1,
  exact h1 h0
end

/- Lemma 1 in the official solution: `f_{X ** Y} = f_X ∘ f_Y` -/
lemma cup_mul_range (X Y : finset ℕ) : nth_notin (X ** Y) = nth_notin X ∘ nth_notin Y :=
begin
  rw ← well_founded.eq_strict_mono_iff_eq_range is_well_order.wf (nth_notin_strict_mono _),
  work_on_goal 2 { exact strict_mono.comp (nth_notin_strict_mono _) (nth_notin_strict_mono _) },
  rw [range_nth_notin_eq_compl, set.range_comp, range_nth_notin_eq_univ_diff, set.image_diff,
      set.image_univ, range_nth_notin_eq_univ_diff, set.diff_diff, ← set.compl_eq_univ_diff,
      compl_inj_iff, cup_mul, coe_union, coe_image],
  exact nth_notin_fn_inj X
end

/- The `cup_mul` operation is associative. -/
theorem cup_mul_assoc (X Y Z : finset ℕ) : X ** Y ** Z = X ** (Y ** Z) :=
  by rw ← nth_notin_inj; repeat { rw cup_mul_range }

/- Lemma 2 in the official solution: if X ** Y = Y ** X and |X| = |Y| then X = Y -/
lemma cup_mul_comm_card_eq {X Y : finset ℕ} (h : X.card = Y.card) (h0 : X ** Y = Y ** X) :
  X = Y :=
begin
  sorry
end

end cup_mul_lemmas



section cup_pow_lemmas

lemma cup_pow_zero (X : finset ℕ) : X ^^ 0 = ∅ := rfl

lemma cup_pow_succ (X : finset ℕ) (k : ℕ) : X ^^ k.succ = X ** X ^^ k :=
  by rw [cup_pow, cup_pow, iterate_succ', comp_app]

/- For any `X : finset ℕ` and `k : ℕ`, `|X^^k| = k |X|`. -/
lemma cup_pow_card (X : finset ℕ) (k : ℕ) : (X ^^ k).card = k * X.card :=
begin
  induction k with k k_ih,
  rw [cup_pow_zero, card_empty, zero_mul],
  rw [cup_pow_succ, cup_mul_card, k_ih, nat.succ_mul, add_comm]
end

/- If `X` commutes with `Y`, then `X^^k` commutes with `Y` for any `k`. -/
lemma cup_pow_comm' {X Y : finset ℕ} (h : X ** Y = Y ** X) (k : ℕ) :
  X ^^ k ** Y = Y ** X ^^ k :=
begin
  induction k with k k_ih,
  rw [cup_pow_zero, cup_mul_empty, empty_cup_mul],
  rw [cup_pow_succ, cup_mul_assoc, k_ih, ← cup_mul_assoc, ← cup_mul_assoc, h]
end

/- If `X` commutes with `Y`, then `X^^k` commutes with `Y^^m` for any `k` and `m`. -/
lemma cup_pow_comm {X Y : finset ℕ} (h : X ** Y = Y ** X) (k m : ℕ) :
  X ^^ k ** Y ^^ m = Y ^^ m ** X ^^ k :=
  cup_pow_comm' (eq_comm.mp (cup_pow_comm' (eq_comm.mp h) m)) k

end cup_pow_lemmas



/- Final solution -/
theorem final_solution (X Y : finset ℕ) (h : X ** Y = Y ** X) : X ^^ Y.card = Y ^^ X.card :=
begin
  refine cup_mul_comm_card_eq _ (cup_pow_comm h _ _),
  rw [cup_pow_card, cup_pow_card, mul_comm]
end

end IMO2017C7
end IMOSL
