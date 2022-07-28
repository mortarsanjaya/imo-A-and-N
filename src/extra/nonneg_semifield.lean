import algebra.field.basic algebra.order.nonneg

namespace IMOSL
namespace extra

/-!
# A semifield instance for F≥0, where F is a linear ordered field

TODO: Delete the instance when mathlib is updated with the same instance
-/

variable {α : Type*}

namespace nonneg

instance semifield [linear_ordered_field α] : semifield {x : α // 0 ≤ x} :=
  subtype.coe_injective.semifield (coe : {x : α // 0 ≤ x} → α)
    rfl rfl (λ x y, rfl) (λ x y, rfl) (λ x, rfl) (λ x y, rfl) (λ _ _, rfl) (λ _ _, rfl)
    (λ x n, begin
      cases le_total n 0 with h h,
      rcases int.exists_eq_neg_of_nat h with ⟨k, rfl⟩,
      rw [zpow_neg, nonneg.coe_inv, zpow_neg, zpow_coe_nat, zpow_coe_nat]; refl,
      lift n to ℕ using h,
      rw [zpow_coe_nat, zpow_coe_nat]; refl
    end)
    (λ _, rfl)
  
end nonneg

end extra
end IMOSL
