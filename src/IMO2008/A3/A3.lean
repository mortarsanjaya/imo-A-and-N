import data.prod.lex order.iterate data.nat.pow data.nat.succ_pred

/-! # IMO 2008 A3 -/

namespace IMOSL
namespace IMO2008A3

open function

def Spanish_couple {α : Type*} [preorder α] (f g : α → α) :=
  (strict_mono f ∧ strict_mono g) ∧ ∀ x, f (g (g x)) < g (f x)





/- ### Part a -/

lemma f_id_not_Spanish_couple {α : Type*} [preorder α] [h : nonempty α] (f : α → α) :
  ¬Spanish_couple f id :=
  λ h0, h.elim $ λ x, lt_irrefl (f x) (h0.2 x)

lemma g_iter_lt_f_of_Spanish_couple {α : Type*} [linear_order α]
    (h : ∀ f : α → α, strict_mono f → ∀ x, x ≤ f x)
    {f g : α → α} (h0 : Spanish_couple f g) :
  ∀ (k : ℕ) (x : α), (g^[k]) x < f x
| 0 x := lt_of_le_of_ne (h f h0.1.1 x) $ λ h1, not_le_of_lt (h0.2 x) $
    (congr_arg g h1.symm).trans_le $ (h g h0.1.2 _).trans (h f h0.1.1 _)
| (k+1) x := h0.1.2.lt_iff_lt.mp $ (h0.2 x).trans' $
    (g_iter_lt_f_of_Spanish_couple k _).trans_eq' $ (iterate_succ_apply' g _ _).symm

lemma add_iterate_le_of_strict_mono_id_lt {f : ℕ → ℕ} (h : strict_mono f)
  {x : ℕ} (h0 : x < f x) : ∀ k : ℕ, x + k ≤ (f^[k]) x
| 0 := x.le_refl
| (k+1) := (nat.add_succ x k).trans_le $ nat.succ_le_of_lt $
    (add_iterate_le_of_strict_mono_id_lt k).trans_lt $ h.iterate k h0

/-- Final solution, part (a) -/
theorem final_solution_part_a (f g : ℕ → ℕ) : ¬Spanish_couple f g :=
  (eq_or_ne g id).elim (λ h h0, f_id_not_Spanish_couple f $ cast (congr_arg _ h) h0) $
    λ h, exists.elim (ne_iff.mp h) $ λ x h0 h1, not_le_of_lt
      (g_iter_lt_f_of_Spanish_couple (λ a, strict_mono.id_le) h1 (f x) x) $
        (nat.le_add_left _ x).trans $ add_iterate_le_of_strict_mono_id_lt
          h1.1.2 (lt_of_le_of_ne (h1.1.2.id_le x) h0.symm) (f x)





/- ### Part b -/

lemma prod_lex_lt_iff {α β : Type*} [preorder α] [preorder β] {p q : α ×ₗ β} :
  p < q ↔ p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2 :=
  prod.lex.lt_iff p q

/-- Final solution, part b (general version) -/
theorem final_solution_part_b_general {β : Type*} [preorder β]
  (φ : β → β) (h : strict_mono φ) (h0 : ∀ x, x < φ x) :
  Spanish_couple (λ p : ℕ ×ₗ β, (p.1.succ, p.2)) (λ p : ℕ ×ₗ β, (p.1, φ^[3^p.1] p.2)) :=
have strict_mono (to_lex : ℕ × β → ℕ ×ₗ β) := prod.lex.to_lex_strict_mono,
⟨⟨λ p q h1, by rwa [prod_lex_lt_iff, nat.succ_lt_succ_iff, nat.succ_inj', ← prod_lex_lt_iff],
λ p q h1, prod_lex_lt_iff.mpr $ (prod_lex_lt_iff.mp h1).imp id $
  λ h1, ⟨h1.1, (h.iterate _ h1.2).trans_eq $ congr_fun (congr_arg _ $ congr_arg (pow 3) h1.1) q.2⟩⟩,
λ x, prod_lex_lt_iff.mpr $ or.inr $ ⟨rfl, (iterate_add_apply φ _ _ x.2).symm.trans_lt $
  h.strict_mono_iterate_of_lt_map (h0 x.2) $ (two_mul _).symm.trans_lt $
    nat.mul_lt_mul_of_pos_right (nat.lt_succ_self 2) (nat.one_le_pow _ 3 $ nat.succ_pos 2)⟩⟩

/-- Final solution, part b (original version: `ℕ ×ₗ ℕ`) -/
theorem final_solution_part_b :
  Spanish_couple (λ p : ℕ ×ₗ ℕ, (p.1.succ, p.2)) (λ p : ℕ ×ₗ ℕ, (p.1, p.2 + 3 ^ p.1)) :=
suffices ∀ p : ℕ ×ₗ ℕ, (p.1, nat.succ^[3 ^ p.1] p.2) = (p.1, p.2 + 3 ^ p.1),
from cast (congr_arg _ $ funext this) $ 
  final_solution_part_b_general nat.succ (λ a b, nat.succ_lt_succ) nat.lt_succ_self,
λ p, prod.ext rfl $ nat.succ_iterate _ _

end IMO2008A3
end IMOSL
