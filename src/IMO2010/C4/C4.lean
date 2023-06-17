import logic.relation algebra.group.pi data.nat.pow tactic.norm_num

/-! # IMO 2010 C4 (P5) -/

namespace IMOSL
namespace IMO2010C4

open function relation

inductive legal_op (N : ℕ) : (ℕ → ℕ) → (ℕ → ℕ) → Prop
| type1 {k : ℕ} (h : k + 1 < N) (f : ℕ → ℕ) :
    legal_op (f + λ i, ite (i = k) 1 0) (f + λ i, ite (i = k + 1) 2 0)
| type2 {k : ℕ} (h : k + 2 < N) (f : ℕ → ℕ) :
    legal_op (f + λ i, ite (i = k) 1 0)
      (λ i, ite (i = k + 1) (f (k + 2)) $ ite (i = k + 2) (f (k + 1)) (f i))

def is_reachable (N : ℕ) := refl_trans_gen (legal_op N)





lemma is_reachable_type1_repeat (N : ℕ) {k : ℕ} (h : k + 1 < N) : ∀ (c : ℕ) (f : ℕ → ℕ),
  is_reachable N (f + λ i, ite (i = k) c 0) (f + λ i, ite (i = k + 1) (2 * c) 0)
| 0 f := by rw mul_zero; simp_rw if_t_t; exact refl_trans_gen.refl
| (c+1) f := begin
  rw nat.mul_succ; simp_rw [ite_add_zero, ← pi.add_def, ← add_assoc],
  refine refl_trans_gen.head (legal_op.type1 h _) _,
  rw [add_right_comm, add_right_comm f _ (λ i, ite _ 2 0)],
  exact is_reachable_type1_repeat c _
end

lemma is_reachable_type1_repeat_ite_else_zero (N : ℕ) {k : ℕ} (h : k + 1 < N) (c : ℕ) :
  is_reachable N (λ i, ite (i = k) c 0) (λ i, ite (i = k + 1) (2 * c) 0) :=
  cast (congr_arg2 _ (zero_add _) (zero_add _)) (is_reachable_type1_repeat N h c 0)

lemma is_reachable_double (N : ℕ) {k : ℕ} (h : k + 2 < N)
  {f : ℕ → ℕ} (h0 : f (k + 1) = f (k + 2)) (c : ℕ) :
  is_reachable N (f + (λ i, ite (i = k) 1 0) + λ i, ite (i = k + 1) c 0)
    (f + λ i, ite (i = k + 1) (2 * c) 0) :=
begin
  refine (is_reachable_type1_repeat N h c _).trans _,
  rw add_right_comm,
  refine (cast (congr_arg _ $ funext $ λ i, _) refl_trans_gen.refl).head (legal_op.type2 h _),
  simp_rw pi.add_apply,
  rw [if_pos rfl, if_neg k.succ.succ_ne_self.symm, add_zero],
  by_cases h1 : i = k + 1,
  rw [if_pos h1, if_pos h1, ← h0, h1],
  rw [if_neg h1, if_neg h1, add_zero],
  by_cases h2 : i = k + 2,
  rw [if_pos h2, h2, h0],
  rw [if_neg h2, if_neg h2, add_zero]
end

lemma is_reachable_two_pow (N : ℕ) {k : ℕ} (h : k + 2 < N) : ∀ (c : ℕ) {f : ℕ → ℕ},
  f (k + 1) = f (k + 2) → is_reachable N (f + λ i, ite (i = k) (c + 1) 0)
    (f + λ i, ite (i = k + 1) (2 ^ (c + 1)) 0)
| 0 f h0 := refl_trans_gen.single $ legal_op.type1 (k.succ.lt_succ_self.trans h) f
| (c+1) f h0 := begin
  rw [funext (λ i, ite_add_zero : ∀ i : ℕ, ite (i = k) (c + 1 + 1) 0 = _),
      ← pi.add_def, ← add_assoc, add_right_comm f, pow_succ],
  refine (is_reachable_two_pow c _).trans (is_reachable_double N h h0 _),
  rw pi.add_def; refine congr_arg2 has_add.add h0 _,
  rw if_neg k.succ_ne_self,
  exact (if_neg $ ne_of_gt $ k.lt_succ_self.trans k.succ.lt_succ_self).symm
end

lemma is_reachable_two_pow_of_ne_zero (N : ℕ) {k : ℕ} (h : k + 2 < N)
  {c : ℕ} (h0 : c ≠ 0) {f : ℕ → ℕ} (h1 : f (k + 1) = f (k + 2)) :
  is_reachable N (f + λ i, ite (i = k) c 0) (f + λ i, ite (i = k + 1) (2 ^ c) 0) :=
  exists.elim (nat.exists_eq_succ_of_ne_zero h0) $
    λ d h0, by rw h0; exact is_reachable_two_pow N h d h1



lemma two_pow_iter_ne_zero : ∀ n : ℕ, (pow 2)^[n] 1 ≠ 0
| 0 := nat.succ_ne_self 0
| (n+1) := by rw [iterate_succ', comp_app]; exact pow_ne_zero _ (nat.succ_ne_zero 1)

lemma is_reachable_two_pow_iter (N : ℕ) {k : ℕ} (h : k + 3 < N) :
  ∀ (c : ℕ) {f : ℕ → ℕ}, f (k + 1) = f (k + 2) → f (k + 2) = f (k + 3) →
    is_reachable N (f + λ i, ite (i = k) (c + 1) 0)
      (f + λ i, ite (i = k + 1) ((pow 2)^[c + 1] 1) 0)
| 0 f h0 h1 := refl_trans_gen.single $
  legal_op.type1 ((nat.lt_add_of_pos_right $ nat.succ_pos 1).trans h) f
| (c+1) f h0 h1 := begin
  rw [funext (λ i, ite_add_zero : ∀ i : ℕ, ite (i = k) (c + 1 + 1) 0 = _),
      ← pi.add_def, ← add_assoc, add_right_comm f, iterate_succ', comp_app],
  have h2 : k < k + 2 := k.lt_succ_self.trans k.succ.lt_succ_self,
  have h3 : (f + λ i, ite (i = k) 1 0) (k + 2) = (f + λ i, ite (i = k) 1 0) (k + 3) :=
    by rw pi.add_def; refine congr_arg2 has_add.add h1 _;
      rw [if_neg $ ne_of_gt h2, if_neg $ ne_of_gt $ h2.trans (k + 2).lt_succ_self],

  refine (is_reachable_two_pow_iter c _ h3).trans _,
  rw pi.add_def; refine congr_arg2 has_add.add h0 _,
  rw [if_neg k.succ_ne_self, if_neg $ ne_of_gt h2],

  refine (is_reachable_two_pow_of_ne_zero N h (two_pow_iter_ne_zero c.succ) h3).trans _,
  replace h3 : k + 2 < N := (k + 2).lt_succ_self.trans h,
  rw add_right_comm,
  refine (cast (congr_arg _ $ funext $ λ i, _) refl_trans_gen.refl).head (legal_op.type2 h3 _),
  simp_rw pi.add_apply,
  rw [if_pos rfl, if_neg k.succ.succ_ne_self.symm, add_zero],
  by_cases h1 : i = k + 1,
  rw [if_pos h1, if_pos h1, ← h0, h1],
  rw [if_neg h1, if_neg h1, add_zero],
  by_cases h2 : i = k + 2,
  rw [if_pos h2, h2, h0],
  rw [if_neg h2, if_neg h2, add_zero]
end

lemma is_reachable_two_pow_iter_of_ne_zero (N : ℕ) {k : ℕ} (h : k + 3 < N) {c : ℕ}
  (h0 : c ≠ 0) {f : ℕ → ℕ} (h1 : f (k + 1) = f (k + 2)) (h2 : f (k + 2) = f (k + 3)) :
  is_reachable N (f + λ i, ite (i = k) c 0) (f + λ i, ite (i = k + 1) ((pow 2)^[c] 1) 0) :=
  exists.elim (nat.exists_eq_succ_of_ne_zero h0) $
    λ d h0, by rw h0; exact is_reachable_two_pow_iter N h d h1 h2

lemma is_reachable_two_pow_iter_ite_else_zero
  (N : ℕ) {k : ℕ} (h : k + 3 < N) {c : ℕ} (h0 : c ≠ 0) :
  is_reachable N (λ i, ite (i = k) c 0) (λ i, ite (i = k + 1) ((pow 2)^[c] 1) 0) :=
  cast (congr_arg2 _ (zero_add _) (zero_add _))
    (is_reachable_two_pow_iter_of_ne_zero N h h0 rfl rfl)



lemma legal_op_type2_idle (N : ℕ) {k : ℕ} (h : k + 2 < N) {f : ℕ → ℕ}
  (h0 : f (k + 1) = f (k + 2)) : legal_op N (f + λ i, ite (i = k) 1 0) f :=
begin
  refine cast (congr_arg _ $ funext $ λ i, _) (legal_op.type2 h f),
  by_cases h1 : i = k + 1,
  rw [if_pos h1, h1, h0],
  rw [if_neg h1, h0, ite_eq_right_iff],
  intros h2; exact congr_arg f h2.symm
end

lemma is_reachable_type2_idle_repeat (N : ℕ) {k : ℕ} (h : k + 2 < N) :
  ∀ (c : ℕ) {f : ℕ → ℕ}, f (k + 1) = f (k + 2) → is_reachable N (f + λ i, ite (i = k) c 0) f
| 0 f h0 := by simp_rw if_t_t; exact refl_trans_gen.refl
| (c+1) f h0 := begin
  simp_rw ite_add_zero; rw [← pi.add_def, ← add_assoc],
  refine (is_reachable_type2_idle_repeat c h0).head (legal_op_type2_idle N h _),
  rw pi.add_def; refine congr_arg2 has_add.add h0 _,
  rw [if_neg k.succ_ne_self, if_neg $ ne_of_gt $ k.lt_succ_self.trans k.succ.lt_succ_self]
end

lemma is_reachable_type2_drain' (N : ℕ) {k : ℕ} (h : k + 2 < N)
  {c d : ℕ} (h0 : d ≤ c) {f : ℕ → ℕ} (h1 : f (k + 1) = f (k + 2)) :
  is_reachable N (f + λ i, ite (i = k) c 0) (f + λ i, ite (i = k) d 0) :=
  exists.elim (le_iff_exists_add.mp h0) $ λ t h0,
begin
  rw h0; simp_rw ite_add_zero; rw [← pi.add_def, ← add_assoc],
  refine is_reachable_type2_idle_repeat N h t _,
  rw pi.add_def; refine congr_arg2 has_add.add h1 _,
  rw [if_neg k.succ_ne_self, if_neg $ ne_of_gt $ k.lt_succ_self.trans k.succ.lt_succ_self]
end

lemma is_reachable_type2_drain (N : ℕ) {k : ℕ} (h : k + 2 < N) {c d : ℕ} (h0 : d ≤ c) :
  is_reachable N (λ i, ite (i = k) c 0) (λ i, ite (i = k) d 0) :=
  cast (congr_arg2 _ (zero_add _) (zero_add _)) (is_reachable_type2_drain' N h h0 rfl)



lemma legal_op_head_ones (N c : ℕ) {k : ℕ} (h : k + 2 < N) :
  legal_op N (λ i, ite (i = k + 2) c $ ite (i < k + 1) 1 0)
    (λ i, ite (i = k + 1) c $ ite (i < k) 1 0) :=
begin
  have h0 : k < k + 2 := k.lt_succ_self.trans k.succ.lt_succ_self,
  refine cast (congr_arg2 _ (funext $ λ i, _) (funext $ λ i, _))
    (legal_op.type2 h $ λ i, ite (i = k + 2) c $ ite (i < k) 1 0),
  
  { rw pi.add_apply,
    by_cases h1 : i = k + 2,
    rw [if_pos h1, if_pos h1, if_neg (ne_of_eq_of_ne h1 $ ne_of_gt h0), add_zero],
    rw [if_neg h1, if_neg h1],
    by_cases h2 : i < k,
    rw [if_pos h2, if_neg (ne_of_lt h2), add_zero, if_pos (h2.trans k.lt_succ_self)],
    rw [if_neg h2, zero_add]; refine if_congr _ rfl rfl,
    rw [nat.lt_succ_iff, le_iff_eq_or_lt],
    exact (or_iff_left h2).symm },

  { rw [if_pos rfl, if_neg (ne_of_lt k.succ.lt_succ_self), if_neg nat.not_succ_lt_self],
    by_cases h1 : i = k + 1,
    rw [if_pos h1, if_pos h1],
    rw [if_neg h1, if_neg h1],
    by_cases h2 : i = k + 2,
    rw [if_pos h2, if_neg (lt_asymm $ lt_of_lt_of_eq h0 h2.symm)],
    rw [if_neg h2, if_neg h2] }
end

lemma is_reachable_head_ones_ite1 (N c : ℕ) : ∀ {k : ℕ}, k + 1 < N →
  is_reachable N (λ i, ite (i = k + 1) c $ ite (i < k) 1 0) (λ i, ite (i = 1) c 0)
| 0 h := refl_trans_gen.refl
| (k+1) h := (is_reachable_head_ones_ite1 $ k.succ.lt_succ_self.trans h).head
    (legal_op_head_ones N c h)

lemma legal_op_ones_ite_3_0 (N : ℕ) :
  legal_op (N + 2) (λ i, ite (i < N + 2) 1 0) (λ i, ite (i = N + 1) 3 $ ite (i < N) 1 0) :=
begin
  refine cast (congr_arg2 _ (funext $ λ i, _) (funext $ λ i, _))
    (legal_op.type1 N.succ.lt_succ_self $ λ i, ite (i = N + 1) 1 $ ite (i < N) 1 0),
 
  { rw pi.add_apply,
    by_cases h0 : i = N + 1,
    rw [if_pos h0, if_pos (lt_of_eq_of_lt h0 N.succ.lt_succ_self),
        if_neg (ne_of_eq_of_ne h0 N.succ_ne_self)],
    have h : N < N + 2 := N.lt_succ_self.trans N.succ.lt_succ_self,
    rw if_neg h0; by_cases h1 : i < N,
    rw [if_pos h1, if_neg (ne_of_lt h1), if_pos (h1.trans h)],
    rw if_neg h1; by_cases h2 : i = N,
    rw [if_pos h2, if_pos (lt_of_eq_of_lt h2 h)],
    rw [if_neg h2, zero_add, eq_comm, (nat.succ_ne_zero 0).ite_eq_right_iff,
        nat.lt_succ_iff_lt_or_eq, not_or_distrib, nat.lt_succ_iff_lt_or_eq, not_or_distrib],
    exact ⟨⟨h1, h2⟩, h0⟩ },

  { rw pi.add_apply,
    by_cases h : i = N + 1,
    rw [if_pos h, if_pos h, if_pos h],
    rw [if_neg h, if_neg h, if_neg h, add_zero] }
end

lemma is_reachable_ones_ite_1_3_0 (N : ℕ) :
  is_reachable (N + 2) (λ i, ite (i < N + 2) 1 0) (λ i, ite (i = 1) 3 0) :=
  (is_reachable_head_ones_ite1 _ 3 N.succ.lt_succ_self).head (legal_op_ones_ite_3_0 N)



lemma is_reachable_six_ones_ite_3_P16_0 :
  is_reachable 6 (λ i, ite (i < 6) 1 0) (λ i, ite (i = 3) ((pow 2)^[16] 1) 0) :=
  (is_reachable_ones_ite_1_3_0 4).trans $
  (is_reachable_two_pow_iter_ite_else_zero 6 (nat.le_succ 5) (nat.succ_ne_zero 2)).trans
    (is_reachable_two_pow_iter_ite_else_zero 6 (nat.lt_succ_self 5) (nat.succ_ne_zero 15))

lemma is_reachable_six_ones_ite_3_A_0 {A : ℕ} (h : A ≤ ((pow 2)^[16] 1)) :
  is_reachable 6 (λ i, ite (i < 6) 1 0) (λ i, ite (i = 3) A 0) :=
  is_reachable_six_ones_ite_3_P16_0.trans
    (is_reachable_type2_drain 6 (nat.lt_succ_self 5) h)

lemma is_reachable_six_ones_ite_5_4A_0 {A : ℕ} (h : A ≤ ((pow 2)^[16] 1)) :
  is_reachable 6 (λ i, ite (i < 6) 1 0) (λ i, ite (i = 5) (2 * (2 * A)) 0) :=
  (is_reachable_six_ones_ite_3_A_0 h).trans $
    (is_reachable_type1_repeat_ite_else_zero 6 (nat.le_succ 5) A).trans
    (is_reachable_type1_repeat_ite_else_zero 6 (nat.lt_succ_self 5) (2 * A))

lemma is_reachable_six_ones_of_four_dvd {A : ℕ} (h : A ≤ 4 * ((pow 2)^[16] 1))
  (h0 : 4 ∣ A) : is_reachable 6 (λ i, ite (i < 6) 1 0) (λ i, ite (i = 5) A 0) :=
begin
  cases h0 with C h0,
  rw [h0, mul_le_mul_left (nat.succ_pos 3)] at h,
  rw [bit0, ← two_mul, mul_assoc] at h0,
  rw h0; exact is_reachable_six_ones_ite_5_4A_0 h
end





lemma two_pow_monotone' (k : ℕ) : ∀ m : ℕ, (pow 2)^[k] 1 ≤ ((pow 2)^[k + m] 1)
| 0 := le_refl _
| (m+1) := by rw [← add_assoc, iterate_succ']; exact (two_pow_monotone' m).trans
    (le_of_lt $ nat.lt_pow_self (nat.lt_succ_self 1) _)

lemma two_pow_monotone {k m : ℕ} (h : k ≤ m) : (pow 2)^[k] 1 ≤ ((pow 2)^[m] 1) :=
  exists.elim (le_iff_exists_add.mp h) $
    λ c h, by rw h; exact two_pow_monotone' k c



lemma big_num_ineq' : 2010 ^ 2010 ^ 2010 ≤ ((pow 2)^[6] 1) :=
begin
  have h : 0 < 2 := nat.succ_pos 1,
  have h0 : 11 ≤ 2 ^ 4 := by norm_num,
  have h1 : 2010 ≤ 2 ^ 11 := by norm_num,
  have h2 : ((pow 2)^[3] 1) = 16 :=
    by iterate 3 { rw [iterate_succ', comp_app] };
      rw [iterate_zero, id, pow_one]; norm_num,

  refine (nat.pow_le_pow_of_le_left h1 _).trans _,
  rw [← pow_mul, iterate_succ'],
  refine nat.pow_le_pow_of_le_right h
    ((nat.mul_le_mul h0 $ nat.pow_le_pow_of_le_left h1 _).trans _),
  rw [← pow_mul, ← pow_add, iterate_succ'],
  refine nat.pow_le_pow_of_le_right h _,
  rw [iterate_succ', comp_app, h2, pow_succ 2 15, two_mul],
  refine nat.add_le_add _ (le_of_le_of_eq (nat.mul_le_mul h0 h1) _),
  rw [bit0, ← two_mul, ← sq]; exact nat.pow_le_pow_of_le_right h (by norm_num),
  rw ← pow_add; exact congr_arg (pow 2) (by norm_num)
end

lemma big_num_ineq : 2010 ^ 2010 ^ 2010 ≤ 4 * ((pow 2)^[16] 1) :=
  big_num_ineq'.trans $ (two_pow_monotone $ nat.bit0_le $
      nat.bit1_le_bit0_iff.mpr $ nat.bit0_le $ nat.le_succ 1).trans
    (nat.le_mul_of_pos_left $ nat.succ_pos 3)

lemma four_dvd_big_num : 4 ∣ 2010 ^ 2010 ^ 2010 :=
  dvd_trans ⟨1005 ^ 2, by rw [bit0, ← two_mul, mul_pow, sq, two_mul]⟩ $
    pow_dvd_pow 2010 $ (nat.bit0_le $ nat.succ_pos 1004).trans $
      nat.le_self_pow (nat.bit0_ne_zero $ nat.succ_ne_zero 1004) 2010

/-- Final solution -/
theorem final_solution :
  is_reachable 6 (λ i, ite (i < 6) 1 0) (λ i, ite (i = 5) (2010 ^ 2010 ^ 2010) 0) :=
  is_reachable_six_ones_of_four_dvd big_num_ineq four_dvd_big_num

end IMO2010C4
end IMOSL
