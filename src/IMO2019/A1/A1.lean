import data.int.order.basic

/-! # IMO 2019 A1 (P1) -/

namespace IMOSL
namespace IMO2019A1

/-- Final solution -/
theorem final_solution {N : ℤ} (h : N ≠ 0) (f : ℤ → ℤ) :
  (∀ a b : ℤ, f (N * a) + N * f b = f (f (a + b))) ↔
    (f = λ _, 0) ∨ ∃ c : ℤ, f = λ n, N * n + c :=
---- `→` direction
⟨λ h0, suffices ∃ q, ∀ n, f n = q * n + f 0,
  from exists.elim this $ λ q h1, or.symm $ (eq_or_ne q N).imp (λ h2, ⟨f 0, h2 ▸ funext h1⟩) $
    λ h2, funext $ λ n, suffices (N - q) * f n = 0,
      from (int.eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_left (sub_ne_zero_of_ne h2.symm),
    suffices N * f n = q * f n, from (N.sub_mul q _).trans (sub_eq_zero_of_eq this),
    add_right_injective (f (N * 0)) $ (h0 0 n).trans $ (h1 _).trans $ (add_comm _ _).trans $
      congr_arg2 _ (congr_arg f N.mul_zero.symm) (n.zero_add.symm ▸ rfl),
-- Now prove linearity
suffices ∀ n : ℤ, f (n + 1) = f n + (f 1 - f 0),
  from let q := f 1 - f 0 in ⟨q, λ n, int.induction_on' n 0
    (q.mul_zero.symm ▸ (f 0).zero_add.symm)
    (λ n _ h1, (this n).trans $ h1.symm ▸ (mul_add_one q n).symm ▸ add_right_comm _ _ _)
    (λ n _ h1, (mul_sub_one q n).symm ▸ add_sub_right_comm (q * n) (f 0) q ▸ h1 ▸
        eq_sub_of_add_eq ((this _).symm.trans $ congr_arg f $ sub_add_cancel n 1))⟩,
have h1 : ∀ n : ℤ, N * (f (n + 1) - f n) = f N - f 0,
  from λ n, (N.mul_sub _ _).trans $ sub_eq_sub_iff_add_eq_add.mpr $
    (add_comm _ _).trans $ N.mul_zero ▸ (h0 _ _).trans
    ((n + 1).zero_add.symm ▸ add_comm 1 n ▸ (h0 _ _).symm.trans (N.mul_one.symm ▸ rfl)),
λ n, have h2 : N * (f (n + 1) - f n - (f (0 + 1) - f 0)) = 0,
  from (N.mul_sub _ _).trans $ sub_eq_zero_of_eq $ (h1 n).trans (h1 0).symm,
eq_add_of_sub_eq' $ eq_of_sub_eq_zero $ (int.eq_zero_or_eq_zero_of_mul_eq_zero h2).resolve_left h,
---- `←` direction
λ h a b, h.elim (λ h, h.symm ▸ (N * 0).zero_add.trans N.mul_zero) $
  λ h, exists.elim h $ λ c h, h.symm ▸ (add_right_comm _ _ _).trans
    (mul_add N (N * a) (N * b + c) ▸ (N * a).add_assoc (N * b) c ▸ mul_add N a b ▸ rfl)⟩

end IMO2019A1
end IMOSL
