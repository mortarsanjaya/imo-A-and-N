import algebra.char_p.basic

namespace IMOSL
namespace extra

/-- For any semifield F of characteristic zero and nontrivial semiring R of
  characteristic non-zero, there is no semiring hom F → R. -/
instance ring_hom_semifield_char_zero_empty {F : Type*} [semifield F] [char_zero F]
    {R : Type*} [nontrivial R] [semiring R] {p : ℕ} [fact (p ≠ 0)] [char_p R p] :
  is_empty (F →+* R) :=
{ false := λ φ,
  begin
    have h := map_nat_cast φ p,
    rw char_p.cast_eq_zero R at h,
    replace h := mul_eq_zero_of_left h (φ p⁻¹),
    rw [← map_mul, mul_inv_cancel, map_one] at h,
    exact one_ne_zero h,
    rw nat.cast_ne_zero,
    exact fact.out (p ≠ 0)
  end }

end extra
end IMOSL
