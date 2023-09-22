import data.nat.basic

/-! # IMO 2010 A6 -/

namespace IMOSL
namespace IMO2010A6

open_locale classical

def good (f g : ℕ → ℕ) := ∀ n : ℕ, f (g n) = (f n).succ

lemma lem1 {f g : ℕ → ℕ} (h : good f g) : ∃ a, ∀ k, (∃ x, f x = k) ↔ a ≤ k :=
  let h0 : ∃ n, ∃ x, f x = n := ⟨f 0, 0, rfl⟩ in
  ⟨nat.find h0, λ k, ⟨nat.find_min' h0, k.le_induction (nat.find_spec h0) $
    λ n _ h1, exists.elim h1 $ λ m h2, ⟨g m, h2 ▸ h m⟩⟩⟩

lemma lem2 {f g : ℕ → ℕ} (h : good f g) {x y : ℕ} (h0 : g x = g y) : f x = f y :=
  nat.succ_injective $ h x ▸ h y ▸ congr_arg f h0 

lemma lem3 {f g : ℕ → ℕ} (h : good g f) {a : ℕ} (h0 : ∀ k, (∃ x, f x = k) ↔ a ≤ k) :
  a < f a :=
((h0 (f a)).mp ⟨a, rfl⟩).lt_or_eq.resolve_right $
  λ h1, (g a).succ_ne_self $ (h a).symm.trans $ congr_arg g h1.symm

lemma lem4 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {k m : ℕ}
  (h1 : ∃ x, f x = k) (h2 : ∃ y, f y = m) (h3 : f k = f m) : k = m :=
  exists.elim h1 $ λ x h1, exists.elim h2 $ λ y h2, h1 ▸ h2 ▸
    lem2 h (nat.succ_injective $ h0 x ▸ h0 y ▸ lem2 h0 (h1.symm ▸ h2.symm ▸ h3))

lemma lem5 : ∀ {f g : ℕ → ℕ}, good f g → good g f → ∀ {a b : ℕ},
  (∀ k : ℕ, (∃ x, f x = k) ↔ a ≤ k) → (∀ k : ℕ, (∃ x, g x = k) ↔ b ≤ k) → a = b :=
suffices ∀ {f g : ℕ → ℕ}, good f g → good g f → ∀ {a b : ℕ}, a ≤ b →
    (∀ k : ℕ, (∃ x, f x = k) ↔ a ≤ k) → (∀ k : ℕ, (∃ x, g x = k) ↔ b ≤ k) → a = b,
  from λ f g h h0 a b, (le_total a b).elim (this h h0) (λ h1 h2 h3, (this h0 h h1 h3 h2).symm),
λ f g h h0 a b h1 h2 h3, h1.antisymm $ (h3 a).mp $
  exists.elim (nat.exists_eq_add_of_lt $ lem3 h0 h2) $ λ t h4,
  exists.elim ((h2 (a + t)).mpr $ a.le_add_right t) $ λ x h5,
⟨x, lem4 h h0 ((h2 _).mpr $ h1.trans $ (h3 _).mp ⟨x, rfl⟩)
  ((h2 _).mpr a.le_refl) ((h x).trans $ h5.symm ▸ h4.symm)⟩

lemma lem6 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) :
  ∃ a : ℕ, (∀ k, (∃ x, f x = k) ↔ a ≤ k) ∧ (∀ k : ℕ, (∃ x, g x = k) ↔ a ≤ k) :=
  exists.elim (lem1 h) $ λ a h1, ⟨a, h1, exists.elim (lem1 h0) $
    λ b h2, (lem5 h h0 h1 h2).symm ▸ h2⟩

lemma lem7 {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) {a : ℕ}
  (h1 : ∀ k : ℕ, (∃ x, f x = k) ↔ a ≤ k) (h2 : ∀ k : ℕ, (∃ x, g x = k) ↔ a ≤ k) :
  f a = a.succ :=
(nat.succ_le_of_lt $ lem3 h0 h1).eq_or_gt.resolve_right $ λ h3,
  exists.elim (nat.exists_eq_add_of_lt h3) $ λ t h4,
  exists.elim ((h1 (a + t)).mpr $ a.le_add_right t) $ λ x h5,
suffices a = g (g x), from exists.elim ((h1 (g x)).mpr $ (h2 _).mp ⟨x, rfl⟩) $
  λ y h6, this.ge.not_lt $ h6 ▸ (h0 y).symm ▸ nat.lt_succ_of_le ((h2 _).mp ⟨y, rfl⟩),
lem4 h h0 ((h1 _).mpr a.le_refl) ((h1 _).mpr $ (h2 _).mp ⟨g x, rfl⟩) $
  h4.trans $ (h (g x)).symm ▸ (h x).symm ▸ h5.symm ▸ congr_arg nat.succ (a.succ_add t)





/-- Final solution -/
theorem final_solution {f g : ℕ → ℕ} (h : good f g) (h0 : good g f) : f = g :=
  exists.elim (lem6 h h0) $ λ a h1,
suffices ∀ n : ℕ, a ≤ n → (f n = n.succ ∧ g n = n.succ),
  from funext $ λ n, nat.succ_injective $ (h n).symm.trans $ (this _ $ (h1.2 _).mp ⟨n, rfl⟩).1,
λ n h2, nat.le_induction ⟨lem7 h h0 h1.1 h1.2, lem7 h0 h h1.2 h1.1⟩
  (λ n h2 h3, ⟨(congr_arg f h3.2.symm).trans $ (h n).trans $ congr_arg nat.succ h3.1,
    (congr_arg g h3.1.symm).trans $ (h0 n).trans $ congr_arg nat.succ h3.2⟩) n h2

end IMO2010A6
end IMOSL
