import algebra.order.positive.ring

/-!
# Integral domains without zero

We construct the class of multiplicative integral monoids `R`
  with cancellative addition that distributes.
It generalizes the subtype of positive elements of a totally ordered commutative ring.
-/

namespace IMOSL
namespace extra

set_option old_structure_cmd true

@[protect_proj]
class domain_without_zero (R : Type*) extends
  cancel_comm_monoid R, add_comm_semigroup R,
    add_left_cancel_semigroup R, add_right_cancel_semigroup R, distrib R

instance {R : Type*} [linear_ordered_comm_ring R] : domain_without_zero {x : R // 0 < x} :=
{ mul_left_cancel := cancel_comm_monoid.mul_left_cancel,
  .. positive.subtype.linear_ordered_cancel_comm_monoid,
  .. positive.subtype.add_comm_semigroup,
  .. positive.subtype.add_left_cancel_semigroup,
  .. positive.subtype.add_right_cancel_semigroup,
  .. positive.subtype.distrib }

end extra
end IMOSL
