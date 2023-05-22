import IMO2012.A5.A5_basic

/-! # IMO 2012 A5, Case 2: `f(-1) = 0` -/

namespace IMOSL
namespace IMO2012A5

set_option profiler true
set_option profiler.threshold 0.05

variables {R S : Type*} [ring R] [ring S] [is_domain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)
include h h0

lemma case2_map_is_even (x : R) : f (-x) = f x :=
  sub_eq_zero.mp $ (map_neg_sub_map2 h x).trans $ mul_eq_zero_of_right (f (x + 1)) h0




end IMO2012A5
end IMOSL
