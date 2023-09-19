import logic.function.iterate order.monotone.basic data.pnat.basic

/-! # IMO 2011 A4 -/

namespace IMOSL
namespace IMO2011A4

open function

/- ### `ℕ` version -/

def good (f g : ℕ → ℕ) :=
  ∀ k, f^[g k + 2] k + ((g^[f k + 1]) k + g (k + 1)) + 1 = f (k + 1)



lemma good_id_zero : good id (λ _, 0) :=
  λ k, congr_arg nat.succ $ congr_arg _ (iterate_succ_apply' _ k k)

lemma eq_zero_of_good_id {g : ℕ → ℕ} (h : good id g) : g = λ _, 0 :=
suffices ∀ k, g^[k + 1] k + g (k + 1) = 0,
  from funext $ λ k, match k with
  | 0 := nat.eq_zero_of_add_eq_zero_right $ this 0
  | (k+1) := nat.eq_zero_of_add_eq_zero_left $ this k
  end,
λ k, nat.add_left_cancel $ nat.add_right_cancel $ (h k).trans $
  (congr_arg nat.succ $ (congr_fun (iterate_id _) _ : id^[g k + 2] k = k)).symm

lemma good_imp_main_ineq {f g : ℕ → ℕ} (h : good f g) (k : ℕ) :
  f^[g k + 2] k < f (k + 1) :=
  (nat.le_add_right _ _).trans_lt $ nat.lt_of_succ_le (h k).le

section main_ineq

variables {f g : ℕ → ℕ} (h : ∀ k, f^[g k + 2] k < f (k + 1))
include h

lemma le_map_of_le : ∀ {k n : ℕ}, k ≤ n → k ≤ f n
| 0 n h0 := (f n).zero_le
| (k+1) 0 h0 := absurd k.succ_pos h0.not_lt
| (k+1) (n+1) h0 := (h n).trans_le' $
    suffices ∀ m, k ≤ (f^[m]) n, from this (g n + 2),
    let h0 := nat.le_of_lt_succ h0 in λ m, nat.rec_on m h0 $
      λ m h1, (le_map_of_le h1).trans_eq (f.iterate_succ_apply' m n).symm

lemma le_iterate_self (n : ℕ) : ∀ m, n ≤ (f^[m]) n
| 0 := n.le_refl
| (m+1) := (le_map_of_le h $ le_iterate_self m).trans_eq (f.iterate_succ_apply' m n).symm

lemma f_strict_mono : strict_mono f :=
  strict_mono_nat_of_lt_succ $ λ n, (h n).trans_le' $ le_iterate_self h (f n) (g n + 1)

lemma main_ineq_imp_eq_id : f = id :=
  let h0 := f_strict_mono h in funext $ λ k, (strict_mono.id_le h0 k).antisymm' $
    nat.le_of_lt_succ $ h0.lt_iff_lt.mp $ (h k).trans_le' $ le_iterate_self h _ (g k)

end main_ineq



/-- Final solution -/
theorem final_solution {f g : ℕ → ℕ} : good f g ↔ f = id ∧ g = λ _, 0 :=
  ⟨λ h, let h0 := main_ineq_imp_eq_id (good_imp_main_ineq h) in
    ⟨h0, eq_zero_of_good_id $ h0 ▸ h⟩,
  λ h, h.1.symm ▸ h.2.symm ▸ good_id_zero⟩





/- ### `ℕ+` (original) version -/

def good_pnat (f g : ℕ+ → ℕ+) :=
  ∀ n, f^[g n + 1] n + (g^[f n] n + g (n + 1)) = f (n + 1) + 1

lemma nat_to_pnat_prop {P : ℕ → Prop} :
  (∀ n : ℕ, P n) ↔ (∀ n : ℕ+, P n.nat_pred) :=
  ⟨λ h n, h n.nat_pred, λ h n, h n.succ_pnat⟩

lemma pnat_nat_conj_iterate (f : ℕ+ → ℕ+) :
  ∀ m n : ℕ, (λ k : ℕ, (f k.succ_pnat).nat_pred)^[m] n = (f^[m] n.succ_pnat).nat_pred
| 0 n := rfl
| (m+1) n := (pnat_nat_conj_iterate m _).trans $
    congr_arg pnat.nat_pred $ congr_arg _ (f n.succ_pnat).succ_pnat_nat_pred 

lemma succ_pnat_succ (n : ℕ) : (n + 1).succ_pnat = n.succ_pnat + 1 := rfl

lemma good_pnat_iff_good {f g : ℕ+ → ℕ+} :
  good_pnat f g ↔ good (λ k, (f k.succ_pnat).nat_pred) (λ k, (g k.succ_pnat).nat_pred) :=
begin
  rw [good_pnat, good, nat_to_pnat_prop],
  refine forall_congr (λ n, _),
  rw [pnat_nat_conj_iterate, pnat_nat_conj_iterate, succ_pnat_succ, pnat.succ_pnat_nat_pred,
      ← add_left_inj 1, pnat.nat_pred_add_one, pnat.nat_pred_add_one, bit0,
      ← (g n).nat_pred.add_assoc, pnat.nat_pred_add_one, nat.add_assoc, add_add_add_comm,
      pnat.nat_pred_add_one, ← add_left_inj 1, nat.add_assoc, nat.add_assoc, add_add_add_comm,
      pnat.nat_pred_add_one, pnat.nat_pred_add_one, ← pnat.add_coe, ← pnat.add_coe,
      ← pnat.one_coe, ← pnat.add_coe (f (n + 1)) 1, pnat.coe_inj]
end



/-- Final solution, `ℕ+` version -/
theorem final_solution_pnat {f g : ℕ+ → ℕ+} : good_pnat f g ↔ f = id ∧ g = λ _, 1 :=
  good_pnat_iff_good.trans $ final_solution.trans $ and_congr
    ⟨λ h, funext $ λ k, pnat.nat_pred_injective $ eq.symm $ (congr_fun h k.nat_pred).symm.trans $
        congr_arg pnat.nat_pred $ congr_arg f k.succ_pnat_nat_pred,
      λ h, funext $ λ k, h.symm ▸ k.nat_pred_succ_pnat⟩
    ⟨λ h, funext $ λ k, pnat.nat_pred_injective $ eq.symm $ (congr_fun h k.nat_pred).symm.trans $
        congr_arg pnat.nat_pred $ congr_arg g k.succ_pnat_nat_pred,
      λ h, funext $ λ k, h.symm ▸ rfl⟩

end IMO2011A4
end IMOSL
