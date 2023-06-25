import data.nat.basic order.monotone.basic

/-!
# Maximum element in a sequence

Let `α` be a linear ordered type and `f : ℕ → α` be a sequence.
We construct the sequence `g : ℕ → α` with `g(n) = max{f(0), f(1), ..., f(n)}` for each `n : ℕ`.
We also prove some of its properties.
-/

namespace IMOSL
namespace extra

variables {α : Type*} [linear_order α] (f : ℕ → α)

def seq_max : ℕ → α
| 0 := f 0
| (n+1) := max (seq_max n) (f $ n+1)

lemma le_seq_max_self : ∀ n, f n ≤ seq_max f n
| 0 := le_refl (f 0)
| (n+1) := le_max_right (seq_max f n) (f $ n+1)

lemma seq_max_mono : monotone (seq_max f) :=
  monotone_nat_of_le_succ $ λ n, le_max_left (seq_max f n) (f $ n+1)

lemma le_seq_max_of_le {m n : ℕ} (h : m ≤ n) : f m ≤ seq_max f n :=
  (le_seq_max_self f m).trans (seq_max_mono f h)

lemma map_zero_le_seq_max (n : ℕ) : f 0 ≤ seq_max f n :=
  le_seq_max_of_le f n.zero_le

lemma exists_map_eq_seq_max : ∀ n : ℕ, ∃ k : ℕ, k ≤ n ∧ f k = seq_max f n
| 0 := ⟨0, le_refl 0, rfl⟩
| (n+1) := (le_total (seq_max f n) (f $ n+1)).elim
    (λ h, ⟨n + 1, le_refl (n + 1), (max_eq_right h).symm⟩)
    (λ h, exists.elim (exists_map_eq_seq_max n) $
      λ k h0, ⟨k, h0.imp n.le_succ.trans' (λ h0, h0.trans (max_eq_left h).symm)⟩)

end extra
end IMOSL
