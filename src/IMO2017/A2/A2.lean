import algebra.ring.basic data.finset.pointwise data.int.interval tactic.ring

/-! # IMO 2017 A2 -/

namespace IMOSL
namespace IMO2017A2

open finset
open_locale pointwise



def sq_add_diff_num {R : Type*} [ring R] (T : finset R) (x : R) :=
  ∃ a b c d : R, a ∈ T ∧ b ∈ T ∧ c ∈ T ∧ d ∈ T ∧ x = (a ^ 2 + b ^ 2) - (c ^ 2 + d ^ 2)

def good {R : Type*} [ring R] (q : R) (T : finset R) :=
  ∀ u v : R, u ∈ T → v ∈ T → sq_add_diff_num T (q * (u * v))

def excellent (k : ℕ) {R : Type*} [ring R] [decidable_eq R] (q : R) :=
  ∀ S : finset R, S.card = k → good q (S - S)







section extra_lemmas

private lemma special_identity {R : Type*} [comm_ring R] (w x y z : R) :
  2 * ((w - x) * (y - z)) = (w - z) ^ 2 + (x - y) ^ 2 - ((w - y) ^ 2 + (x - z) ^ 2) :=
  by ring

private lemma set_coe_image_sub {R : Type*} [ring R] [decidable_eq R] (S T : finset ℤ) :
  image (coe : ℤ → R) (S - T) = image coe S - image coe T :=
begin
  ext x; simp only [mem_image, mem_sub]; split,
  rintros ⟨a, ⟨x, y, h, h0, rfl⟩, rfl⟩;
    exact ⟨x, y, ⟨x, h, rfl⟩, ⟨y, h0, rfl⟩, by rw int.cast_sub⟩,
  rintros ⟨x, y, ⟨x, h, rfl⟩, ⟨y, h0, rfl⟩, rfl⟩;
    exact ⟨x - y, ⟨x, y, h, h0, rfl⟩, by rw int.cast_sub⟩
end

private lemma card_image_coe {R : Type*} [ring R] [decidable_eq R] [char_zero R] (T : finset ℤ) :
  (image (coe : ℤ → R) T).card = T.card :=
  card_image_of_injective T int.cast_injective

private lemma mem_diff_doubleton_mul {R : Type*} [ring R] [decidable_eq R]
  {x u v : R} (h : u ∈ ({0, x, -x} : finset R)) (h0 : v ∈ ({0, x, -x} : finset R)) :
  u * v ∈ ({0, x ^ 2, -x ^ 2} : finset R) :=
begin
  simp_rw [mem_insert, mem_singleton] at h h0 ⊢,
  rcases h with rfl | h,
  left; rw zero_mul,
  rcases h0 with rfl | h0,
  left; rw mul_zero,
  rcases h with rfl | rfl; rcases h0 with rfl | rfl,
  right; left; rw ← sq,
  right; right; rw [mul_neg, ← sq],
  right; right; rw [neg_mul, ← sq],
  right; left; rw [neg_mul_neg, ← sq]
end


variables {G : Type*} [add_group G] [decidable_eq G]

private lemma self_diff_singleton {T : finset G} (h : T.card = 1) : T - T = {0} :=
  by rw card_eq_one at h; rcases h with ⟨a, rfl⟩; rw [singleton_sub_singleton, sub_self]

private lemma self_diff_doubleton {T : finset G} (h : T.card = 2) :
  ∃ g : G, T - T = {0, g, -g} :=
begin
  rw card_eq_two at h,
  rcases h with ⟨a, b, -, rfl⟩; use a - b,
  simp_rw [neg_sub, insert_eq, union_sub, sub_union, singleton_sub_singleton, sub_self],
  rw [union_assoc, union_comm,← union_assoc, union_right_idem, union_comm]
end

end extra_lemmas





section sq_add_diff_num

variables {R : Type*} [ring R] {T : finset R} {x : R}

private lemma zero_is_sq_add_diff_num (h : T.nonempty) : sq_add_diff_num T 0 :=
  by cases h with x h; exact ⟨x, x, x, x, h, h, h, h, (sub_self (x ^ 2 + x ^ 2)).symm⟩

private lemma neg_is_sq_add_diff_num (h : sq_add_diff_num T x) :
  sq_add_diff_num T (-x) :=
  by rcases h with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩;
    exact ⟨c, d, a, b, hc, hd, ha, hb, neg_sub (a ^ 2 + b ^ 2) (c ^ 2 + d ^ 2)⟩

private lemma sq_is_sq_add_diff_num (h : x ∈ T) (h0 : (0 : R) ∈ T) :
  sq_add_diff_num T (x ^ 2) :=
  ⟨x, 0, 0, 0, h, h0, h0, h0, by rw [sq (0 : R), zero_mul, add_zero, add_zero, sub_zero]⟩

private lemma two_mul_sq_is_sq_add_diff_num (h : x ∈ T) (h0 : (0 : R) ∈ T) :
  sq_add_diff_num T (2 * x ^ 2) :=
  ⟨x, x, 0, 0, h, h, h0, h0, by rw [← two_mul, sq (0 : R), zero_mul, add_zero, sub_zero]⟩

private lemma is_sq_add_diff_num_imp_eq_int_cast [decidable_eq R]
  {T : finset ℤ} (h : sq_add_diff_num (image coe T) x) :
  ∃ n : ℤ, x = n :=
begin
  rcases h with ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩,
  rw mem_image at ha hb hc hd,
  rcases ha with ⟨w, hw, rfl⟩,
  rcases hb with ⟨x, hx, rfl⟩,
  rcases hc with ⟨y, hy, rfl⟩,
  rcases hd with ⟨z, hz, rfl⟩,
  refine ⟨w ^ 2 + x ^ 2 - (y ^ 2 + z ^ 2), _⟩,
  simp_rw [int.cast_sub, int.cast_add, int.cast_pow]
end

private lemma cast_is_sq_add_diff_num_imp [decidable_eq R] [char_zero R]
  {T : finset ℤ} {n : ℤ} (h : sq_add_diff_num (image coe T) (n : R)) :
  sq_add_diff_num T n :=
begin
  rcases h with ⟨a, b, c, d, ha, hb, hc, hd, h⟩,
  rw mem_image at ha hb hc hd,
  rcases ha with ⟨w, hw, rfl⟩,
  rcases hb with ⟨x, hx, rfl⟩,
  rcases hc with ⟨y, hy, rfl⟩,
  rcases hd with ⟨z, hz, rfl⟩,
  simp_rw [← int.cast_pow, ← int.cast_add, ← int.cast_sub, int.cast_inj] at h,
  exact ⟨w, x, y, z, hw, hx, hy, hz, h⟩
end

end sq_add_diff_num





section good

variables {R : Type*} [ring R]

private lemma good_any_empty (q : R) : good q ∅ :=
  λ u v h _, by exfalso; exact h

private lemma good_any_singleton_zero (q : R) : good q {0} :=
  λ u v h _, by rw mem_singleton at h; rw [h, zero_mul, mul_zero];
    exact zero_is_sq_add_diff_num (singleton_nonempty 0)

private lemma good_neg_any {q : R} {T : finset R} (h : good q T) : good (-q) T :=
  λ u v h0 h1, by rw neg_mul; exact neg_is_sq_add_diff_num (h u v h0 h1)

private lemma good_zero_any (T : finset R) : good 0 T :=
  λ u _ h _, ⟨u, u, u, u, h, h, h, h, by rw [sub_self, zero_mul]⟩

private lemma good_one_self_diff_doubleton [decidable_eq R] (x : R) :
  good (1 : R) {0, x, -x} :=
begin
  intros u v h h0; rw one_mul,
  replace h := mem_diff_doubleton_mul h h0,
  generalize_hyp : u * v = y at h ⊢; clear h0 u v,
  have h0 : sq_add_diff_num ({0, x, -x} : finset R) (x ^ 2) :=
    sq_is_sq_add_diff_num (mem_insert_of_mem (mem_insert_self x _)) (mem_insert_self 0 _),
  simp_rw [mem_insert, mem_singleton] at h,
  rcases h with rfl | rfl | rfl,
  exacts [zero_is_sq_add_diff_num (insert_nonempty 0 {x, -x}), h0, neg_is_sq_add_diff_num h0]
end

private lemma good_two_self_diff_doubleton [decidable_eq R] (x : R) :
  good (2 : R) {0, x, -x} :=
begin
  intros u v h h0,
  replace h := mem_diff_doubleton_mul h h0,
  generalize_hyp : u * v = y at h ⊢; clear h0 u v,
  have h0 : sq_add_diff_num ({0, x, -x} : finset R) (2 * x ^ 2) :=
    two_mul_sq_is_sq_add_diff_num (mem_insert_of_mem (mem_insert_self x _)) (mem_insert_self 0 _),
  simp_rw [mem_insert, mem_singleton] at h,
  rcases h with rfl | rfl | rfl,
  rw mul_zero; exact zero_is_sq_add_diff_num (insert_nonempty 0 {x, -x}),
  exact h0,
  rw mul_neg; exact neg_is_sq_add_diff_num h0
end

private lemma good_two_self_diff {R : Type*} [comm_ring R] [decidable_eq R] (T : finset R) :
  good 2 (T - T) :=
begin
  intros u v h h0; unfold sq_add_diff_num,
  simp_rw mem_sub at h h0 ⊢,
  rcases h with ⟨w, x, hw, hx, rfl⟩,
  rcases h0 with ⟨y, z, hy, hz, rfl⟩,
  exact ⟨w - z, x - y, w - y, x - z, ⟨w, z, hw, hz, rfl⟩, ⟨x, y, hx, hy, rfl⟩,
    ⟨w, y, hw, hy, rfl⟩, ⟨x, z, hx, hz, rfl⟩, special_identity w x y z⟩
end

private lemma good_one_mem_imp_eq_int_cast [decidable_eq R]
  {q : R} {T : finset ℤ} (h : good q (image coe T)) (h0 : (1 : ℤ) ∈ T) :
  ∃ n : ℤ, q = n :=
begin
  replace h0 : (1 : R) ∈ image coe T :=
    by rw ← int.cast_one; exact mem_image_of_mem coe h0,
  replace h := h _ _ h0 h0,
  rw [mul_one, mul_one] at h; exact is_sq_add_diff_num_imp_eq_int_cast h
end

private lemma good_cast_cast_imp_good [decidable_eq R] [char_zero R]
  {n : ℤ} {T : finset ℤ} (h : good (n : R) (image coe T)) :
  good n T :=
begin
  intros u v h0 h1,
  replace h := h u v (mem_image_of_mem coe h0) (mem_image_of_mem coe h1),
  simp_rw ← int.cast_mul at h; exact cast_is_sq_add_diff_num_imp h
end

private lemma good_int_bound {n : ℤ} {T : finset ℤ} (h : good n T) (h0 : ∃ k : ℤ, k ≠ 0 ∧ k ∈ T) :
  n ∈ ({0, 1, -1, 2, -2} : finset ℤ) :=
begin
  ---- Get the maximum modulus integer in `T`
  -- ...
  sorry
end

private lemma not_good_one {T : finset ℤ}
  (h : (1 : ℤ) ∈ T) (h0 : (4 : ℤ) ∈ T) (h1 : ∀ x : ℤ, x ∈ T → odd x ∨ 4 ∣ x) :
  ¬good (1 : ℤ) T :=
begin
  sorry
end

end good





section main_results

private lemma excellent_any_zero (R : Type*) [ring R] [decidable_eq R] (k : ℕ) :
  excellent k (0 : R) :=
  λ T _, good_zero_any (T - T)

private lemma excellent_any_two (R : Type*) [comm_ring R] [decidable_eq R] (k : ℕ) :
  excellent k (2 : R) :=
  λ T _, good_two_self_diff T

variables {R : Type*} [ring R] [decidable_eq R]

private lemma excellent_any_neg (k : ℕ) {q : R} (h : excellent k q) : excellent k (-q) :=
  λ T h0, good_neg_any (h T h0)

private lemma excellent_ge_two_imp [char_zero R]
  {k : ℕ} (h : 2 ≤ k) {q : R} (h0 : excellent k q) :
  q ∈ ({0, 1, -1, 2, -2} : finset R) :=
begin
  ---- First find some `T : finset ℤ` of size `k` such that `1 ∈ T - T`
  obtain ⟨T, rfl, h1⟩ : ∃ T : finset ℤ, T.card = k ∧ (1 : ℤ) ∈ T - T :=
  begin
    refine ⟨Ico (0 : ℤ) (k : ℤ), by rw [int.card_Ico, sub_zero, int.to_nat_coe_nat], _⟩,
    rw mem_sub; refine ⟨1, 0, _, _, sub_zero 1⟩,
    rw mem_Ico; exact ⟨int.one_nonneg, nat.one_lt_cast.mpr h⟩,
    rw mem_Ico; exact ⟨le_refl 0, nat.cast_pos.mpr (lt_of_lt_of_le two_pos h)⟩
  end,

  ---- Show that `q = ↑n` for some integer `n ∈ {0, 1, -1, 2, -2}`
  replace h0 := h0 (image coe T) (card_image_coe T),
  rw ← set_coe_image_sub at h0,
  obtain ⟨n, rfl⟩ := good_one_mem_imp_eq_int_cast h0 h1,
  replace h0 := good_int_bound (good_cast_cast_imp_good h0) ⟨1, one_ne_zero, h1⟩,

  ---- Finishing
  convert mem_image_of_mem (coe : ℤ → R) h0; clear h h0 h1 n T,
  simp_rw [image_insert, image_singleton, int.cast_neg],
  rw [int.cast_zero, int.cast_one, int.cast_two]
end

private lemma excellent_ge_three_imp [char_zero R] {k : ℕ} (h : 3 ≤ k) :
  ∀ {q : R}, excellent k q → q ∈ ({0, 2, -2} : finset R) :=
begin
  ---- Reduce to showing that `1 : R` is not `k`-excellent
  suffices h0 : ¬excellent k (1 : R),
  { intros q h1,
    replace h := excellent_ge_two_imp (le_trans (nat.le_succ 2) h) h1,
    simp_rw [mem_insert, mem_singleton] at h ⊢,
    rcases h with rfl | rfl | rfl | rfl | rfl,
    left; refl,
    exfalso; exact h0 h1,
    exfalso; rw ← neg_neg (1 : R) at h0,
    exact h0 (excellent_any_neg k h1),
    right; left; refl,
    right; right; refl },

  ---- Reduce to finding `T : finset ℤ` such that `1, 4 ∈ T - T` and
  ----   all elements of `T - T` are either odd or divisible by `4`
  rsuffices ⟨T, h0, h1, h2, h3⟩ : ∃ T : finset ℤ,
    T.card = k ∧ (1 : ℤ) ∈ T - T ∧ (4 : ℤ) ∈ T - T ∧ ∀ x : ℤ, x ∈ T - T → odd x ∨ 4 ∣ x,
  { intros h4; replace h4 := h4 (image coe T) (by rw [card_image_coe, h0]),
    rw [← set_coe_image_sub, ← int.cast_one] at h4,
    exact not_good_one h1 h2 h3 (good_cast_cast_imp_good h4) },

  ---- Find the desired `T`
  sorry
end

end main_results







/-- Final solution, `k = 0` -/
theorem final_solution_k_eq_0 {R : Type*} [ring R] [decidable_eq R] :
  ∀ q : R, excellent 0 q :=
  λ q T h, by rw [card_eq_zero.mp h, sub_empty]; exact good_any_empty q



/-- Final solution, `k = 1` -/
theorem final_solution_k_eq_1 {R : Type*} [ring R] [decidable_eq R] :
  ∀ q : R, excellent 1 q :=
  λ q T h, by rw self_diff_singleton h; exact good_any_singleton_zero q



/-- Final solution, `k = 2` -/
theorem final_solution_k_eq_2 {R : Type*} [ring R] [decidable_eq R] [char_zero R] :
  ∀ q : R, excellent 2 q ↔ q ∈ ({0, 1, -1, 2, -2} : finset R) :=
begin
  ---- Reduce to showing that `1, 2 : R` are `2`-excellent
  rsuffices ⟨h0, h1⟩ : excellent 2 (1 : R) ∧ excellent 2 (2 : R),
  { intros q; refine ⟨excellent_ge_two_imp (le_refl 2), λ h, _⟩,
    simp_rw [mem_insert, mem_singleton] at h,
    rcases h with rfl | rfl | rfl | rfl | rfl,
    exacts [excellent_any_zero R 2, h0, excellent_any_neg 2 h0, h1, excellent_any_neg 2 h1] },
  
  ---- Now show that both `1, 2 : R` are `2`-excellent
  refine ⟨λ T h, _, λ T h, _⟩;
    replace h := self_diff_doubleton h;
    cases h with x h; rw h,
  exacts [good_one_self_diff_doubleton x, good_two_self_diff_doubleton x]
end



/-- Final solution, `k ≥ 3` -/
theorem final_solution_k_ge_3 {k : ℕ} (h : 3 ≤ k)
  {R : Type*} [comm_ring R] [decidable_eq R] [char_zero R] :
  ∀ q : R, excellent k q ↔ q ∈ ({0, 2, -2} : finset R) :=
begin
  have h0 : excellent k (2 : R) := λ T _, good_two_self_diff T,
  refine λ q, ⟨excellent_ge_three_imp h, λ h1, _⟩,
  simp_rw [mem_insert, mem_singleton] at h1,
  rcases h1 with rfl | rfl | rfl,
  exacts [excellent_any_zero R k, h0, excellent_any_neg k h0]
end

end IMO2017A2
end IMOSL
