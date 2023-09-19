import algebra.module.hom data.list.basic

/-! # IMO 2009 C3 -/

namespace IMOSL
namespace IMO2009C3

/- ### Extra lemmas -/

lemma map_nsmul_add_nsmul {M N : Type*} [add_comm_monoid M] [add_comm_monoid N]
  (φ : M →+ N) (p q : ℕ) (a b : M) : φ (p • a + q • b) = p • φ a + q • φ b :=
  (φ.map_add _ _).trans $ congr_arg2 _ (φ.map_nsmul a p) (φ.map_nsmul b q)





section general

open add_monoid_hom

/- ### Start of the problem -/

variables (M : Type*) [add_comm_monoid M] {α : Type*} (p q : α → ℕ)

def f (a : α) : M × M →+ M × M :=
  (snd M M).prod (p a • fst M M + q a • snd M M)

lemma f_apply (a : α) (y z : M) : f M p q a (y, z) = (z, p a • y + q a • z) := rfl



def list_f : list α → M × M →+ M × M :=
  list.foldr (comp ∘ f M p q) (id $ M × M)

lemma list_f_nil : list_f M p q [] = id (M × M) := rfl

lemma list_f_cons (a : α) (l : list α) :
  list_f M p q (a :: l) = (f M p q a).comp (list_f M p q l) := rfl

lemma list_f_append : ∀ l1 l2 : list α,
  list_f M p q (l1 ++ l2) = (list_f M p q l1).comp (list_f M p q l2)
| [] l2 := l2.nil_append.symm ▸ (id_comp _).symm
| (a :: l1) l2 := (list_f_cons M p q a _).trans $
    (list_f_append l1 l2).symm ▸ (comp_assoc _ _ _).symm

lemma list_f_concat (l : list α) (a : α) :
  list_f M p q (l.concat a) = (list_f M p q l).comp (f M p q a) :=
  (l.concat_eq_append a).symm ▸ list_f_append M p q l [a]

lemma list_f_concat_apply (l : list α) (a : α) (y z : M) :
  list_f M p q (l.concat a) (y, z) = list_f M p q l (z, p a • y + q a • z) :=
  by rw [list_f_concat, comp_apply, f_apply]





/-- Final solution -/
theorem final_solution (x y z : M) (h : ∀ a : α, p a • x + q a • y = z) :
  ∀ l : list α, (list_f M p q l.reverse (y, z)).2 = (list_f M p q l (y, z)).2
| [] := rfl
| [b] := rfl
| (b :: a :: l) := let φ := list_f M p q (a :: l).reverse in
calc (list_f M p q (b :: a :: l).reverse (y, z)).2
= (φ (z, p b • y + q b • z)).2 :
  by rw [list.reverse_cons', list_f_concat_apply]
... = (φ (p b • x + q b • y, p b • y + q b • z)).2 : by rw ← h b
... = (φ $ p b • (x, y) + q b • (y, z)).2 : rfl
... = p b • (list_f M p q (a :: l).reverse (x, y)).2 + q b • (φ (y, z)).2 :
  congr_arg prod.snd $ map_nsmul_add_nsmul φ _ _ _ _
... = p b • (list_f M p q l (y, z)).2 + q b • (list_f M p q (a :: l) (y, z)).2 :
  congr_arg2 _ (by rw [list.reverse_cons', list_f_concat_apply, h a, final_solution l])
    (congr_arg _ $ final_solution (a :: l))
... = _ : rfl

end general





/- ### Original version of the problem -/

def nat_p : bool → ℕ | ff := 2 | tt := 3
def nat_q : bool → ℕ | ff := 3 | tt := 1

/-- Final solution, original version -/
theorem final_solution_nat : ∀ l : list bool,
  (list_f ℕ nat_p nat_q l.reverse (1, 7)).2 = (list_f ℕ nat_p nat_q l (1, 7)).2 :=
  final_solution ℕ nat_p nat_q 2 1 7 $ λ a, match a with | ff := rfl | tt := rfl end

end IMO2009C3
end IMOSL
