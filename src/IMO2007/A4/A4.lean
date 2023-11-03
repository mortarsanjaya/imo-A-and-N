import algebra.order.positive.ring

/-! # IMO 2007 A4 -/

namespace IMOSL
namespace IMO2007A4

variables {G : Type*} [linear_ordered_add_comm_group G]

/-! ## Extra lemmas -/

lemma exists_add_of_lt {x y : {x : G // 0 < x}} (h : x < y) :
  ∃ c : {x : G // 0 < x}, x + c = y :=
  ⟨⟨y - x, sub_pos_of_lt h⟩, subtype.coe_injective $ add_sub_cancel'_right x y⟩

lemma pos_lt_self_add {x y : {x : G // 0 < x}} : x < x + y :=
  lt_add_of_pos_right _ y.2

lemma pos_lt_add_self {x y : {x : G // 0 < x}} : x < y + x :=
  lt_add_of_pos_left _ y.2



/-! ## Start of the problem -/

def good (f : {x : G // 0 < x} → {x : G // 0 < x}) :=
  ∀ x y : {x : G // 0 < x}, f (x + f y) = f (x + y) + f y

def good' (g : {x : G // 0 < x} → {x : G // 0 < x}) :=
  ∀ t y : {x : G // 0 < x}, y < t → g (t + g y) = g t + y



lemma add_self_is_good : good (λ x : {x : G // 0 < x}, x + x) :=
  λ x y, (add_assoc _ _ _).symm.trans $ congr_arg2 _
    ((add_right_comm _ _ _).trans (add_add_add_comm _ _ _ _)) rfl

lemma good_imp_id_lt {f : {x : G // 0 < x} → {x : G // 0 < x}} (h : good f)
  (y : {x : G // 0 < x}) : y < f y :=
(lt_trichotomy y (f y)).resolve_right $ λ h0, h0.elim
---- Case `f(y) = y`
(λ h0, (h y y).not_lt $ h0 ▸ lt_add_of_pos_right _ y.2)
---- Case `f(y) < y`
(λ h0, exists.elim (exists_add_of_lt h0) $ λ x h0, (h x y).not_lt $
  add_comm (f y) x ▸ h0.symm ▸ pos_lt_add_self)

lemma good_imp_good'_add_id {f : {x : G // 0 < x} → {x : G // 0 < x}} (h : good f) :
  ∃ g : {x : G // 0 < x} → {x : G // 0 < x}, (∀ y, f y = g y + y) ∧ good' g :=
let g : {x : G // 0 < x} → {x : G // 0 < x} :=
  λ x, ⟨f x - x, sub_pos_of_lt (good_imp_id_lt h x)⟩,
h0 : ∀ y, f y = g y + y := λ y, subtype.coe_injective $ (sub_add_cancel (f y).1 y).symm in
⟨g, h0, λ t y h1, exists.elim (exists_add_of_lt h1) $ λ x h1, h1 ▸
  (add_rotate y x (g y)).symm ▸ (add_assoc x (g y) y).symm ▸ h0 y ▸
  add_left_injective (x + f y) ((h0 _).symm.trans $ (h _ _).trans $
    add_assoc (g (y + x) + y) x (f y) ▸ add_comm y x ▸
    (h0 (y + x)).symm ▸ add_assoc (g (y + x)) y x ▸ add_assoc _ _ _)⟩



section good'

variables {g : {x : G // 0 < x} → {x : G // 0 < x}} (h : good' g)
include h

lemma good'_imp_injective : g.injective :=
  λ a b h0, add_right_injective (g (a + b)) $
    (h _ _ pos_lt_self_add).symm.trans $ h0.symm ▸ h _ _ pos_lt_add_self

lemma good'_imp_additive (x y : {x : G // 0 < x}) : g (x + y) = g x + g y :=
have h0 : ∃ t, x + y < t := ⟨x + y + x, pos_lt_self_add⟩,
exists.elim h0 $ λ t h0, add_right_injective t $ good'_imp_injective h $
  (h _ _ h0).trans $ (add_assoc _ _ _).symm.trans $ (h t x $ pos_lt_self_add.trans h0) ▸
  add_assoc t (g x) (g y) ▸ (h _ _ $ pos_lt_add_self.trans $ h0.trans pos_lt_self_add).symm

lemma good'_imp_strict_mono : strict_mono g :=
  λ t u h0, exists.elim (exists_add_of_lt h0) $ λ c h0,
    h0 ▸ (good'_imp_additive h t c).symm ▸ pos_lt_self_add

lemma good'_imp_id : g = id :=
funext $ λ y, have h0 : g (g y) = y := add_right_injective (g (y + y)) $
  (good'_imp_additive h _ _).symm.trans (h _ _ pos_lt_self_add),
let X := good'_imp_strict_mono h in
((lt_trichotomy (g y) y).resolve_left (λ h1, (h1.trans' $ X h1).ne h0)).resolve_right
  (λ h1, (h1.trans $ X h1).ne.symm h0)

end good'





/-- Final solution -/
theorem final_solution {f : {x : G // 0 < x} → {x : G // 0 < x}} :
  good f ↔ f = λ x, x + x :=
⟨λ h, exists.elim (good_imp_good'_add_id h) $ λ g h, funext $ λ x,
  (h.1 x).trans $ (good'_imp_id h.2).symm ▸ rfl,
λ h, h.symm ▸ add_self_is_good⟩

end IMO2007A4
end IMOSL
