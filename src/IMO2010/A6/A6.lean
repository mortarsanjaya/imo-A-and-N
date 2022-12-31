import data.nat.order.basic data.set.image

/-! # IMO 2010 A6 -/

namespace IMOSL
namespace IMO2010A6

open_locale classical

def good (f g : ℕ → ℕ) := ∀ n : ℕ, f (g n) = (f n).succ

private lemma lem1 {f g : ℕ → ℕ} (h : good f g) : ∃ a : ℕ, ∀ k : ℕ, k ∈ set.range f ↔ a ≤ k :=
begin
  have h0 : ∃ n, n ∈ set.range f := ⟨f 0, set.mem_range_self 0⟩,
  use nat.find h0; refine λ k, ⟨nat.find_min' h0, _⟩,
  apply nat.le_induction; clear k,
  exact nat.find_spec h0,
  rintros n - ⟨k, h1⟩,
  use g k; rw [h, h1]
end

private lemma lem2 {f g : ℕ → ℕ} (h : good f g) {x y : ℕ} (h0 : g x = g y) : f x = f y :=
  by rw [← nat.succ_inj', ← h, ← h, h0]

private lemma lem3 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {x y : ℕ} :
  f x = f y ↔ g x = g y := ⟨lem2 h0, lem2 h⟩

private lemma lem4 {f g : ℕ → ℕ} (h : good g f) {a : ℕ}
  (ha : ∀ k : ℕ, k ∈ set.range f ↔ a ≤ k) : a.succ ≤ f a :=
begin
  have h1 : a ≤ f a := by rw ← ha; use a,
  rw [le_iff_eq_or_lt, or_comm] at h1,
  cases h1 with h1 h1,
  rwa nat.succ_le_iff,
  replace h := h a,
  rw [← h1, nat.succ_eq_add_one] at h,
  exfalso; exact nat.succ_ne_self (g a) h.symm
end

private lemma lem5 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {a b : ℕ} (h1 : a ≤ b)
  (ha : ∀ k : ℕ, k ∈ set.range f ↔ a ≤ k) (hb : ∀ k : ℕ, k ∈ set.range g ↔ b ≤ k) : a = b :=
begin
  obtain ⟨x, h2⟩ : ∃ x : ℕ, f a = f x + 1 :=
  begin
    have h2 := lem4 h0 ha,
    rw [nat.succ_eq_add_one, le_iff_exists_add] at h2,
    cases h2 with c h2,
    obtain ⟨x, h3⟩ : a + c ∈ set.range f := (ha (a + c)).mpr le_self_add,
    use x; rw [h2, h3, add_right_comm]
  end,
  obtain ⟨c, h3⟩ := (ha a).mpr (le_refl a),
  obtain ⟨d, h4⟩ := (ha (g x)).mpr (le_trans h1 (by rw ← hb; use x)),
  rw [← nat.succ_eq_add_one, ← h, ← h3, ← h4, lem3 h h0, h0, h0, nat.succ_inj', lem3 h0 h] at h2,
  refine le_antisymm h1 _,
  rw [← h3, h2, h4, ← hb]; use x
end

private lemma lem6 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {a b : ℕ}
  (ha : ∀ k : ℕ, k ∈ set.range f ↔ a ≤ k) (hb : ∀ k : ℕ, k ∈ set.range g ↔ b ≤ k) : a = b :=
begin
  cases le_total a b with h1 h1,
  exact lem5 h h0 h1 ha hb,
  rw lem5 h0 h h1 hb ha
end

private lemma lem7 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {a : ℕ}
  (ha : ∀ k : ℕ, k ∈ set.range f ↔ a ≤ k) (ha' : ∀ k : ℕ, k ∈ set.range g ↔ a ≤ k) : f a = a.succ :=
begin
  have h1 := lem4 h0 ha,
  rw [le_iff_eq_or_lt, ← nat.succ_le_iff] at h1,
  cases h1 with h1 h1,
  rw h1,
  obtain ⟨x, h2⟩ : ∃ x : ℕ, f a = f x + 1 + 1 :=
  begin
    rw [nat.succ_eq_add_one, nat.succ_eq_add_one, add_assoc, le_iff_exists_add] at h1,
    cases h1 with c h1,
    obtain ⟨x, h2⟩ : a + c ∈ set.range f := (ha (a + c)).mpr le_self_add,
    use x; rw [h1, h2, add_right_comm]
  end,
  rw [← nat.succ_eq_add_one, ← nat.succ_eq_add_one, ← h, ← h] at h2,
  obtain ⟨c, h3⟩ := (ha a).mpr (le_refl a),
  obtain ⟨d, h4⟩ := (ha (g (g x))).mpr (by rw ← ha'; use (g x)),
  rw [← h3, ← h4, lem3 h h0, h0, h0, nat.succ_inj', lem3 h0 h] at h2,
  obtain ⟨e, h5⟩ := (ha (g x)).mpr (by rw ← ha'; use x),
  rw [h3, h4, ← h5, h0, eq_comm] at h2,
  replace h2 := le_of_le_of_eq (nat.succ_le_succ_iff.mpr (by rw ← ha'; use e)) h2,
  rw [nat.succ_eq_add_one, add_le_iff_nonpos_right, ← not_lt] at h2,
  exfalso; exact h2 one_pos
end



/-- Final solution -/
theorem final_solution {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) : f = g :=
begin
  cases lem1 h with a h1,
  cases lem1 h0 with b h2,
  have h3 := lem6 h h0 h1 h2; subst h3,
  suffices : ∀ n : ℕ, a ≤ n → (f n = n.succ ∧ g n = n.succ),
    ext n; rw [← nat.succ_inj', ← h, (this (g n) (by rw ← h2; use n)).left],
  intros n; apply nat.le_induction; clear n,
  exact ⟨lem7 h h0 h1 h2, lem7 h0 h h2 h1⟩,
  rintros n h3 ⟨h4, h5⟩; split,
  rw [← nat.succ_eq_add_one, ← h5, h, h4, h5],
  rw [← nat.succ_eq_add_one, ← h4, h0, h5, h4]
end

end IMO2010A6
end IMOSL
