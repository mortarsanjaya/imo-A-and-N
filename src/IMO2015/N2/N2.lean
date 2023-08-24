import data.nat.choose.basic data.nat.gcd.basic tactic.norm_num

/-! # IMO 2015 N2 -/

namespace IMOSL
namespace IMO2015N2

/- ### Extra lemmas -/

lemma add_dvd_mul_comm {a b : ℕ} : a + b ∣ a * b ↔ b + a ∣ b * a :=
  iff_of_eq $ congr_arg2 has_dvd.dvd (a.add_comm b) (a.mul_comm b)

lemma add_dvd_mul_iff_add_dvd_sq {a b : ℕ} : a + b ∣ a * b ↔ a + b ∣ a * a :=
  let h : a + b ∣ a * a + a * b :=
    (dvd_mul_left _ a).trans $ dvd_of_eq $ mul_add a a b in
  ⟨λ h0, (nat.dvd_add_left h0).mp h, λ h0, (nat.dvd_add_right h0).mp h⟩

lemma add_dvd_mul_pos_imp_one_lt_right
  {a b : ℕ} (h : a + b ∣ a * b) (h0 : 0 < a) (h1 : 0 < b) : 1 < b :=
  (lt_or_eq_of_le $ nat.succ_le_of_lt h1).resolve_right $ λ h2, absurd h $
    h2 ▸ a.mul_one.symm ▸ nat.not_dvd_of_pos_of_lt h0 a.lt_succ_self

lemma add_dvd_mul_pos_imp_one_lt_left
  {a b : ℕ} (h : a + b ∣ a * b) (h0 : 0 < a) (h1 : 0 < b) : 1 < a :=
  add_dvd_mul_pos_imp_one_lt_right (add_dvd_mul_comm.mp h) h1 h0

lemma asc_factorial_mono_left {m n : ℕ} (h : m ≤ n) :
  ∀ k : ℕ, m.asc_factorial k ≤ n.asc_factorial k
| 0 := nat.le_refl 1
| (k+1) := nat.mul_le_mul (nat.succ_le_succ $ nat.add_le_add_right h _)
    (asc_factorial_mono_left k)

lemma asc_factorial_mono_right (k : ℕ) : monotone k.asc_factorial :=
  λ m n h, nat.le_induction (le_refl _)
    (λ n h h0, h0.trans $ nat.le_mul_of_pos_left $ (k + n).succ_pos) n h

lemma asc_factorial_succ' (n k : ℕ) :
  n.asc_factorial k.succ = (n + 1) * (n + 1).asc_factorial k :=
  nat.asc_factorial_succ.trans (n.succ_asc_factorial k).symm

lemma one_add_coprime_of_dvd {a b : ℕ} (h : a ∣ b) : (1 + b).coprime a :=
  exists.elim h $ λ c h, h.symm ▸
    (nat.coprime_add_mul_left_left 1 _ _).mpr a.coprime_one_left

lemma add_succ_dvd_asc_factorial_of_lt (n : ℕ) {k m : ℕ} (h : m < k) :
  n + m + 1 ∣ n.asc_factorial k :=
  nat.le_induction ⟨n.asc_factorial m, rfl⟩
    (λ k _ h, h.trans $ ⟨n + k + 1, mul_comm _ _⟩) k h





/- ### Start of the problem -/

def good (a b : ℕ) := a.factorial + b.factorial ∣ a.factorial * b.factorial

lemma good_comm {a b : ℕ} : good a b ↔ good b a :=
  add_dvd_mul_comm

lemma good_iff {a b : ℕ} :
  good a b ↔ a.factorial + b.factorial ∣ a.factorial * a.factorial :=
  add_dvd_mul_iff_add_dvd_sq

lemma good_imp_one_lt_left {a b : ℕ} (h : good a b) : 1 < a :=
  nat.one_lt_factorial.mp $
    add_dvd_mul_pos_imp_one_lt_left h a.factorial_pos b.factorial_pos

lemma good_add_iff_weak {a c : ℕ} :
  good a (a + c) ↔ 1 + a.asc_factorial c ∣ a.factorial :=
  good_iff.trans $ a.factorial_mul_asc_factorial c ▸
    mul_one_add a.factorial (a.asc_factorial c) ▸
    nat.mul_dvd_mul_iff_left a.factorial_pos

lemma good_add_imp {a c : ℕ} (h : good a (a + c)) : c < a :=
  lt_of_not_le $ λ h0, absurd (good_add_iff_weak.mp h) $
    nat.not_dvd_of_pos_of_lt a.factorial_pos $ nat.lt_one_add_iff.mpr $
    a.zero_asc_factorial.symm.trans_le $ (asc_factorial_mono_left a.zero_le a).trans $
    asc_factorial_mono_right a h0

lemma good_add_add_iff {d c : ℕ} :
  good (c + d) (c + d + c) ↔ 1 + (c + d).asc_factorial c ∣ c.asc_factorial d :=
  good_add_iff_weak.trans $ c.factorial_mul_asc_factorial d ▸
    (one_add_coprime_of_dvd ⟨_, (c + d).asc_factorial_eq_factorial_mul_choose c⟩).dvd_mul_left

lemma good_add_add_bound {d c : ℕ} (h : good (c + d) (c + d + c)) : c + 2 ≤ d :=
begin
  have h0 := good_imp_one_lt_left h,
  rw good_add_add_iff at h,
  have h1 := (nat.pow_le_pow_of_le_left (c + d).le_succ c).trans_lt
    (((c + d).pow_succ_le_asc_factorial c).trans_lt $
    (nat.one_add_le_iff.mp $ nat.le_of_dvd (c.asc_factorial_pos d) h).trans_le $
      c.asc_factorial_le_pow_add d),
  rw [nat.pow_lt_iff_lt_right h0, ← nat.succ_le_iff, le_iff_eq_or_lt] at h1,
  revert h1, refine (or_iff_right $ λ h1, _).mp,

  -- Final step: Prove `1 + (2c + 2)(2c + 3) … (3c + 1) ∤ (c + 1)(c + 2) … (2c + 1)`.
  rw [← h1, asc_factorial_succ'] at h,
  refine nat.not_dvd_of_pos_of_lt (c.succ.asc_factorial_pos c)
    (nat.lt_one_add_iff.mpr $ asc_factorial_mono_left le_add_self c)
    ((one_add_coprime_of_dvd _).dvd_mul_left.mp h),
  clear h0 h1 h d, cases c, exact dvd_refl 1,
  refine dvd_trans ⟨2, _⟩ (add_succ_dvd_asc_factorial_of_lt _ c.succ_pos),
  rw [add_zero, add_right_comm, mul_two]
end

lemma good_add_add_eq_case {c : ℕ} (h : good (c + (c + 2)) (c + (c + 2) + c)) :
  c = 0 ∨ c = 1 :=
suffices c < 2, from (lt_or_eq_of_le $ nat.le_of_lt_succ this).imp nat.lt_one_iff.mp id,
lt_of_not_le $ λ h0, begin
  revert h,
  rw [good_add_add_iff, asc_factorial_succ', asc_factorial_succ', mul_left_comm,
      (one_add_coprime_of_dvd $ dvd_trans ⟨2, _⟩ $
        add_succ_dvd_asc_factorial_of_lt (c + (c + 2)) h0).dvd_mul_left],
  work_on_goal 2 { rw [add_assoc, add_right_comm, ← mul_two] },
  rw [le_iff_eq_or_lt, ← nat.succ_le_iff] at h0,
  rcases h0 with rfl | h0,
  
  ---- Case `c = 2`: Solve via "hard code" `RHS (= 90) % LHS (= 57) = 33 ≠ 0`
  exact λ h, absurd (nat.mod_eq_zero_of_dvd h) (nat.bit1_ne_zero 16),
  
  ---- Case `c ≥ 3`
  suffices : c + 2 + 1 ∣ (c + (c + 2)).asc_factorial c,
  { have h1 := asc_factorial_succ' (c + 2) c.pred,
    have h2 := pos_of_gt (nat.lt_of_succ_le h0),
    rw nat.succ_pred_eq_of_pos h2 at h1,
    rw [h1, mul_left_comm, (one_add_coprime_of_dvd this).dvd_mul_left],
    refine nat.not_dvd_of_pos_of_lt (nat.mul_pos c.succ_pos $ nat.asc_factorial_pos _ _)
      ((nat.mul_le_mul_right _ $ c.add_le_add_left $ nat.succ_pos 2).trans_lt _),
    rw [← h1, ← nat.succ_eq_one_add, nat.lt_succ_iff],
    exact asc_factorial_mono_left le_add_self c },

  -- Remains to show that `c + 3 ∣ (2c + 2).asc_factorial c` for `c ≥ 3`
  rw le_iff_exists_add' at h0,
  rcases h0 with ⟨c, rfl⟩, cases c,
  -- Case `c = 3`
  { rw [nat.zero_add, nat.asc_factorial_eq_factorial_mul_choose],
    exact dvd_mul_right 6 _ },
  { refine dvd_trans ⟨2, _⟩ (add_succ_dvd_asc_factorial_of_lt _ $
      nat.lt_add_of_pos_left c.succ_pos),
    rw [add_right_comm (c.succ + nat.succ 2) _ (nat.succ 2), add_assoc, mul_two] }
end





/-- Final solution -/
theorem final_solution {a b : ℕ} (h : good a b) :
  2 * b + 2 ≤ 3 * a ∧ (2 * b + 2 = 3 * a ↔ a = 2 ∧ b = 2 ∨ a = 4 ∧ b = 5) :=
suffices 2 * b + 2 ≤ 3 * a ∧ (2 * b + 2 = 3 * a → a = 2 ∧ b = 2 ∨ a = 4 ∧ b = 5),
  from ⟨this.1, this.2, λ h0, h0.elim (λ h0, h0.1.symm ▸ h0.2.symm ▸ rfl)
    (λ h0, h0.1.symm ▸ h0.2.symm ▸ rfl)⟩,
(lt_or_le b a).elim
---- `a > b`
(λ h0, suffices 2 * b + 2 < 3 * a, from ⟨this.le, λ h1, absurd h1 this.ne⟩,
(add_lt_add_of_lt_of_le (nat.mul_lt_mul_of_pos_left h0 $ nat.succ_pos 1)
  (nat.succ_le_of_lt $ good_imp_one_lt_left h)).trans_eq (add_one_mul 2 a).symm)
---- `a ≤ b`
(λ h0, begin
  rw le_iff_exists_add at h0,
  rcases h0 with ⟨c, rfl⟩,
  rcases exists_add_of_le (good_add_imp h).le with ⟨d, rfl⟩,
  rw [bit1, mul_add, add_one_mul 2, add_assoc, add_le_add_iff_left,
    add_right_inj, two_mul, add_assoc, add_le_add_iff_left, add_right_inj],
  refine ⟨good_add_add_bound h, λ h0, _⟩,
  subst h0; exact (good_add_add_eq_case h).imp
    (λ h0, h0.symm ▸ ⟨rfl, rfl⟩) (λ h0, h0.symm ▸ ⟨rfl, rfl⟩)
end)

end IMO2015N2
end IMOSL
