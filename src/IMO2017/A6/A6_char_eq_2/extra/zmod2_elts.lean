import data.zmod.basic

namespace IMOSL
namespace IMO2017A6
namespace extra

/-- The elements of zmod 2 are just 0 and 1. -/
lemma zmod2_elts (c : zmod 2) : c = 0 ∨ c = 1 :=
begin
  fin_cases c,
  left; refl,
  right; refl
end

end extra
end IMO2017A6
end IMOSL
