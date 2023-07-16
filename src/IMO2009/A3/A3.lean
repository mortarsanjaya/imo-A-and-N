import data.pnat.basic data.nat.periodic extra.seq_max

/-! # IMO 2009 A3 (P5) -/

namespace IMOSL
namespace IMO2009A3

open function

section extra_lemmas

private lemma exists_sup_fn_fin (f : ℕ → ℕ) (c : ℕ) : ∃ K : ℕ, ∀ n : ℕ, n < c → f n ≤ K :=
⟨extra.seq_max f c, λ n h, extra.le_seq_max_of_le f (le_of_lt h)⟩

private lemma pnat_to_nat_prop {P : ℕ+ → Prop} :
  (∀ n : ℕ+, P n) ↔ (∀ n : ℕ, P n.succ_pnat) :=
  ⟨λ h n, h n.succ_pnat, λ h n, by rw ← pnat.succ_pnat_nat_pred n; exact h _⟩

private lemma pnat_to_nat_prop2 {P : ℕ+ → ℕ+ → Prop} :
  (∀ m n : ℕ+, P m n) ↔ (∀ m n : ℕ, P m.succ_pnat n.succ_pnat) :=
  by rw pnat_to_nat_prop; refine forall_congr (λ m, _); rw pnat_to_nat_prop

private lemma succ_pnat_add_succ_pnat (m n : ℕ) :
  m.succ_pnat + n.succ_pnat = (m + n).succ_pnat + 1 :=
  by rw [← pnat.coe_inj, pnat.add_coe, pnat.add_coe, nat.succ_pnat_coe, nat.succ_pnat_coe,
         nat.succ_pnat_coe, nat.add_succ, nat.succ_add, positive.coe_one]

private lemma pnat_add_sub_cancel (m n : ℕ+) : m + n - n = m :=
  by rw [← add_right_inj n, pnat.add_sub_of_lt (n.lt_add_left m), add_comm]

end extra_lemmas





/-- Final solution, `nat` version -/
theorem final_solution_nat (f : ℕ → ℕ) :
  ((∀ x y : ℕ, f (y + f x) ≤ f y + x)
    ∧ (∀ x y : ℕ, x ≤ f y + f (y + f x))
    ∧ (∀ x y : ℕ, f y ≤ f (y + f x) + x))
      ↔ f = λ x, x :=
begin
  ---- First, the easier direction: `←`
  symmetry; split,
  { rintros rfl,
    refine ⟨λ x y, le_refl (y + x), λ x y, _, λ x y, _⟩,
    rw ← add_assoc; exact le_add_self,
    rw add_assoc; exact le_self_add },

  ---- For the harder case, first prove that `f(0) = 0`
  rintros ⟨h, h0, h1⟩,
  replace h1 : f 0 = 0 :=
  begin
    contrapose! h0; rw ← zero_lt_iff at h0,
    obtain ⟨K, h2⟩ := exists_sup_fn_fin f (f 0),
    refine ⟨K + K + 1, 0, nat.lt_succ_of_le (add_le_add (h2 0 h0) _)⟩,
    rw [zero_add, ← periodic.map_mod_nat (λ y, le_antisymm (h 0 y) (h1 0 y))],
    exact h2 _ (nat.mod_lt (f (K + K + 1)) h0)
  end,

  ---- Now get `f(f(x)) = x` for all `x`
  replace h0 : ∀ x : ℕ, f (f x) = x :=
  begin
    intros x; apply le_antisymm,
    replace h := h x 0,
    rwa [h1, zero_add, zero_add] at h,
    replace h0 := h0 x 0,
    rwa [h1, zero_add, zero_add] at h0
  end,

  ---- Get `f(x + f(1)) ≤ f(x) + 1` and then `f(1) = 1`
  replace h := h 1,
  have h2 : f 1 = 1 :=
  begin
    suffices : ∀ n : ℕ, f (n * f 1) = n,
    { replace this := congr_arg f (this (f 1)),
      rw [h0, h0] at this,
      exact nat.eq_one_of_mul_eq_one_left this },
      
    intros n; induction n using nat.strong_induction_on with n n_ih; cases n,
    rw [zero_mul, h1],
    replace h := h (n * f 1),
    rw [n_ih n n.lt_succ_self, ← add_one_mul, le_iff_eq_or_lt, nat.lt_succ_iff] at h,
    revert h; refine (or_iff_left_of_imp (λ h, _)).mp,
    replace n_ih := congr_arg f (n_ih _ (lt_of_le_of_lt h n.lt_succ_self)),
    rw [h0, h0, mul_eq_mul_right_iff] at n_ih,
    revert n_ih; refine (or_iff_left _).mp,
    rw ← h1; apply_fun f,
    rw [h0, h0]; exact one_ne_zero
  end,

  ---- Finish
  funext x; induction x using nat.strong_induction_on with x x_ih; cases x,
  exact h1,
  replace h := h x,
  rw [h2, x_ih x x.lt_succ_self, le_iff_eq_or_lt, nat.lt_succ_iff] at h,
  revert h; refine (or_iff_left_of_imp (λ h, _)).mp,
  replace x_ih := congr_arg f (x_ih _ (lt_of_le_of_lt h x.lt_succ_self)),
  rwa [h0, h0] at x_ih
end



/-- Final solution, `pnat` version -/
theorem final_solution_pnat (f : ℕ+ → ℕ+) :
  ((∀ x y : ℕ+, f (y + f x - 1) < f y + x)
    ∧ (∀ x y : ℕ+, x < f y + f (y + f x - 1))
    ∧ (∀ x y : ℕ+, f y < f (y + f x - 1) + x))
      ↔ f = λ x, x :=
begin
  obtain ⟨g, rfl⟩ : ∃ g : ℕ → ℕ, f = λ x, (g x.nat_pred).succ_pnat :=
    ⟨λ x, (f x.succ_pnat).nat_pred,
      funext (λ x, by rw [pnat.succ_pnat_nat_pred, pnat.succ_pnat_nat_pred])⟩,
  simp_rw [pnat_to_nat_prop2, funext_iff, pnat_to_nat_prop, nat.nat_pred_succ_pnat,
           nat.succ_pnat_inj, ← funext_iff, succ_pnat_add_succ_pnat, pnat_add_sub_cancel,
           nat.nat_pred_succ_pnat, pnat.lt_add_one_iff, nat.succ_pnat_le_succ_pnat],
  exact final_solution_nat g
end

end IMO2009A3
end IMOSL
