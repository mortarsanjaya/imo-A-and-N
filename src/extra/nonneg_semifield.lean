import algebra.field.basic algebra.order.nonneg data.real.nnreal

namespace IMOSL
namespace extra

/-!
# A linear ordered semifield instance for F≥0, where F is a linear ordered field

TODO:
1. Delete the instance when mathlib is updated with the same instance.
2. Delete the specific semifield instance for ℝ≥0.
-/

namespace nonneg

instance linear_ordered_semifield {α : Type*} [linear_ordered_field α] :
    linear_ordered_semifield {x : α // 0 ≤ x} :=
  subtype.coe_injective.linear_ordered_semifield (coe : {x : α // 0 ≤ x} → α)
    rfl rfl (λ _ _, rfl) (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
    (λ x n, begin
      cases le_total n 0 with h h,
      rcases int.exists_eq_neg_of_nat h with ⟨k, rfl⟩,
      rw [zpow_neg, nonneg.coe_inv, zpow_neg, zpow_coe_nat, zpow_coe_nat]; refl,
      lift n to ℕ using h,
      rw [zpow_coe_nat, zpow_coe_nat]; refl
    end)
    (λ _, rfl) (λ _ _, rfl) (λ _ _, rfl)
  
end nonneg



namespace nnreal

/-- Semifield instance for ℝ≥0; delete if possible -/
noncomputable instance linear_ordered_semifield : linear_ordered_semifield nnreal :=
  nonneg.linear_ordered_semifield

end nnreal

end extra
end IMOSL
