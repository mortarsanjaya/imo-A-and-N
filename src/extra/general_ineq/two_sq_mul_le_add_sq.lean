import algebra.group_power.order algebra.order.field.canonical.defs

/-!
# The inequality `4ab ≤ (a + b)^2` over ordered rings

This result is put separately mainly to reduce imports in inequality files.
-/

namespace IMOSL
namespace extra

lemma general_two_sq_mul_le_add_sq {R : Type*} [ordered_comm_semiring R]
  (h : ∀ a b : R, 2 * a * b ≤ a ^ 2 + b ^ 2) (a b : R) :
  2 ^ 2 * (a * b) ≤ (a + b) ^ 2 :=
  by rw [add_sq', sq, mul_assoc, two_mul, ← mul_assoc]; exact add_le_add_right (h a b) _

lemma ring_two_sq_mul_le_add_sq {R : Type*} [linear_ordered_comm_ring R] (a b : R) :
  2 ^ 2 * (a * b) ≤ (a + b) ^ 2 :=
  general_two_sq_mul_le_add_sq two_mul_le_add_sq a b



section semifield

variables {F : Type*} [canonically_linear_ordered_semifield F]

private lemma canonical_two_mul_le_add_sq :
  ∀ a b : F, 2 * a * b ≤ a ^ 2 + b ^ 2 :=
suffices ∀ a b : F, a ≤ b → 2 * a * b ≤ a ^ 2 + b ^ 2,
  from λ a b, (le_total a b).elim (this a b)
    (λ h, (mul_right_comm _ _ _).trans_le $ (this b a h).trans_eq (add_comm _ _)),
λ a b h, exists.elim (exists_add_of_le h) $ λ c h, le_iff_exists_add.mpr
  ⟨c ^ 2, by rw [h, add_sq, ← add_assoc, ← add_assoc, sq, ← add_mul, ← two_mul, mul_add]⟩

lemma canonical_semifield_two_sq_mul_le_add_sq (a b : F) :
  2 ^ 2 * (a * b) ≤ (a + b) ^ 2 :=
  general_two_sq_mul_le_add_sq canonical_two_mul_le_add_sq a b

end semifield

end extra
end IMOSL
