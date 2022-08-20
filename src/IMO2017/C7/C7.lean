import data.nat.nth

/-! # IMO 2017 C7 -/

namespace IMOSL
namespace IMO2017C7

open finset function

noncomputable def nth_notin (X : finset ℕ) := nat.nth (λ n, n ∉ X)
noncomputable def cup_mul (X Y : finset ℕ) := X ∪ image (nth_notin X) Y
noncomputable def cup_pow (X : finset ℕ) (k : ℕ) := nat.iterate (λ Y, cup_mul X Y) k ∅
local infix ` ** `:80 := cup_mul
local infix ` ^^ `:100 := cup_pow



section strict_mono

private lemma strict_mono_eq_at_large_comm {f g : ℕ → ℕ} (hf : strict_mono f) (hg : strict_mono g)
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
  rw [← h3, ← h4],
  { replace h1 := h1 (g k) h4,
    rw [← comp_app f, h0, comp_app] at h1,
    exact hg.injective h1 },
  { replace h1 := h1 (f k) h3,
    rw [← comp_app g, ← h0, comp_app] at h1,
    exact hf.injective h1 }
end

end strict_mono



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

private lemma nth_notin_empty : nth_notin ∅ = id :=
  by simp [nth_notin, nth_true]

private lemma count_notin_large {n : ℕ} (h : X.sup id < n) :
  nat.count (λ x, x ∉ X) (n + X.card) = n :=
begin
  have h0 := congr_arg card (filter_union_filter_neg_eq (λ x, x ∈ X) (range (n + X.card))),
  rw [card_range, card_union_eq, ← nat.count_eq_card_filter_range,
      ← nat.count_eq_card_filter_range, nat.count_eq_card_fintype] at h0,
  work_on_goal 2 { rw disjoint_iff_inter_eq_empty, exact filter_inter_filter_neg_eq _ _ },
  rw [← add_left_inj X.card, add_comm]; convert h0 using 2; clear h0,
  suffices : ∀ k : ℕ, k ∈ X ↔ (k < n + X.card ∧ k ∈ X),
    rw eq_comm; convert fintype.subtype_card X this, -- Why doesn't it work with `exact`???
  simp only [iff_and_self]; intros k h0,
  refine lt_of_le_of_lt (le_sup h0) (lt_trans h _),
  rw [lt_add_iff_pos_right, pos_iff_ne_zero, ne.def, card_eq_zero],
  rintros rfl; exact h0
end

private lemma nth_notin_large {n : ℕ} (h : X.sup id < n) : nth_notin X n = n + X.card :=
begin
  have h0 := nat_finset_infinite_compl X,
  rw [nth_notin, eq_comm, eq_iff_le_not_lt]; split,
  rw [← nat.count_le_iff_le_nth _ h0, count_notin_large X h],
  rw [← nat.succ_le_iff, ← nat.count_le_iff_le_nth _ h0, nat.count_succ, count_notin_large X h,
      add_le_iff_nonpos_right, nonpos_iff_eq_zero, ← ne.def, ite_ne_right_iff, and_comm],
  refine ⟨one_ne_zero, λ h1, _⟩,
  replace h1 : id (n + X.card) ≤ X.sup id := le_sup h1,
  rw [id.def, ← not_lt] at h1,
  exact h1 (lt_of_lt_of_le h le_self_add)
end

end finset_lemmas



section cup_mul_lemmas

lemma cup_mul_empty (X : finset ℕ) : X ** ∅ = X :=
  by rw [cup_mul, image_empty, union_empty]
  
lemma empty_cup_mul (X : finset ℕ) : ∅ ** X = X :=
  by rw [cup_mul, empty_union, nth_notin_empty, image_id]

/-- For any `X Y : finset ℕ`, `|X ** Y| = |X| + |Y|`. -/
lemma cup_mul_card (X Y : finset ℕ) : (X ** Y).card = X.card + Y.card :=
begin
  rw [cup_mul, card_disjoint_union, card_image_of_injective Y (nth_notin_fn_inj X)],
  rw disjoint_right; intros a h1 h0,
  rw ← mem_coe at h1,
  replace h1 : a ∈ set.range (nth_notin X) := coe_image_subset_range h1,
  rw [range_nth_notin_eq_compl, set.mem_compl_eq, finset.mem_coe] at h1,
  exact h1 h0
end

/-- Lemma 1 in the official solution: `f_{X ** Y} = f_X ∘ f_Y` -/
lemma cup_mul_range (X Y : finset ℕ) : nth_notin (X ** Y) = nth_notin X ∘ nth_notin Y :=
begin
  rw ← well_founded.eq_strict_mono_iff_eq_range is_well_founded.wf (nth_notin_strict_mono _),
  work_on_goal 2 { exact strict_mono.comp (nth_notin_strict_mono _) (nth_notin_strict_mono _) },
  rw [range_nth_notin_eq_compl, set.range_comp, range_nth_notin_eq_univ_diff, set.image_diff,
      set.image_univ, range_nth_notin_eq_univ_diff, set.diff_diff, ← set.compl_eq_univ_diff,
      compl_inj_iff, cup_mul, coe_union, coe_image],
  exact nth_notin_fn_inj X
end

/-- The `cup_mul` operation is associative. -/
theorem cup_mul_assoc (X Y Z : finset ℕ) : X ** Y ** Z = X ** (Y ** Z) :=
  by rw ← nth_notin_inj; repeat { rw cup_mul_range }

/-- Lemma 2 in the official solution: if X ** Y = Y ** X and |X| = |Y| then X = Y -/
lemma cup_mul_comm_card_eq {X Y : finset ℕ} (h : X.card = Y.card) (h0 : X ** Y = Y ** X) : X = Y :=
begin
  rw ← nth_notin_inj at h0 ⊢,
  rw [cup_mul_range, cup_mul_range] at h0,
  refine strict_mono_eq_at_large_comm (nth_notin_strict_mono X) (nth_notin_strict_mono Y) _ h0,
  use max (X.sup id) (Y.sup id) + 1; intros n h1,
  rw [nat.succ_le_iff, max_lt_iff] at h1,
  cases h1 with h1 h2,
  rw [nth_notin_large X h1, nth_notin_large Y h2, h]
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
