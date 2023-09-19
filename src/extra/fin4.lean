/-!
# `fin4`

We construct `fin4` as an explicit type with `4` elements.
The only instance we put on `fin4` is `decidable_eq`.
-/

namespace IMOSL
namespace extra

inductive fin4
| i1 : fin4
| i2 : fin4
| i3 : fin4
| i4 : fin4

namespace fin4

instance : decidable_eq fin4
| i1 i1 := is_true rfl
| i1 i2 := is_false $ λ h, fin4.no_confusion h
| i1 i3 := is_false $ λ h, fin4.no_confusion h
| i1 i4 := is_false $ λ h, fin4.no_confusion h
| i2 i1 := is_false $ λ h, fin4.no_confusion h
| i2 i2 := is_true rfl
| i2 i3 := is_false $ λ h, fin4.no_confusion h
| i2 i4 := is_false $ λ h, fin4.no_confusion h
| i3 i1 := is_false $ λ h, fin4.no_confusion h
| i3 i2 := is_false $ λ h, fin4.no_confusion h
| i3 i3 := is_true rfl
| i3 i4 := is_false $ λ h, fin4.no_confusion h
| i4 i1 := is_false $ λ h, fin4.no_confusion h
| i4 i2 := is_false $ λ h, fin4.no_confusion h
| i4 i3 := is_false $ λ h, fin4.no_confusion h
| i4 i4 := is_true rfl

end fin4

end extra
end IMOSL
