import data.nat.parity field_theory.finite.basic algebra.is_prime_pow

/-! # IMO 2020 N4, Generalized Version (Properties of `F` and `S_p`) -/

namespace IMOSL
namespace IMO2020N4

open finset function



section extra_lemmas

lemma not_dvd_of_coprime {p : ℕ} (h : p ≠ 1) {x : ℕ} (h0 : x.coprime p) : ¬p ∣ x :=
begin
  rintros ⟨d, rfl⟩,
  replace h0 := h0.coprime_mul_right,
  rw nat.coprime_self at h0,
  exact h h0
end

lemma two_pow_lt_Mersenne {k m : ℕ} (h : 1 < k) (h0 : m < k) : 2 ^ m < 2 ^ k - 1 :=
begin
  rw lt_iff_exists_add at h; rcases h with ⟨n, h, rfl⟩,
  rw [← nat.succ_eq_one_add, nat.lt_succ_iff] at h0,
  rw [lt_tsub_iff_right, pow_add, pow_one, two_mul],
  exact add_lt_add_of_le_of_lt (pow_mono one_le_two h0) (nat.one_lt_two_pow n h)
end

end extra_lemmas



section order_two

variables {p : ℕ} (h : odd p)
include h

lemma two_coprime_p : nat.coprime 2 p :=
  by rwa [nat.prime_two.coprime_iff_not_dvd, nat.two_dvd_ne_zero, ← nat.odd_iff]

lemma exists_two_mod_eq_one : ∃ k : ℕ, 0 < k ∧ 2 ^ k ≡ 1 [MOD p] :=
  ⟨p.totient, nat.totient_pos (odd.pos h), nat.modeq.pow_totient (two_coprime_p h)⟩

def order_two_mod_p := nat.find (exists_two_mod_eq_one h)

lemma order_two_mod_p_pos : 0 < order_two_mod_p h :=
  (nat.find_spec (exists_two_mod_eq_one h)).1

lemma two_pow_order_two_mod_p_eq_one : 2 ^ order_two_mod_p h ≡ 1 [MOD p] :=
  (nat.find_spec (exists_two_mod_eq_one h)).2

lemma two_pow_mod_p_eq_one_iff (k : ℕ) : 2 ^ k ≡ 1 [MOD p] ↔ order_two_mod_p h ∣ k :=
begin
  let T := order_two_mod_p h,
  have h0 : 0 < T := order_two_mod_p_pos h,
  have h1 : 2 ^ T ≡ 1 [MOD p] := two_pow_order_two_mod_p_eq_one h,
  obtain ⟨q, r, h0, rfl⟩ : ∃ q r : ℕ, r < T ∧ r + q * T = k :=
    ⟨k / T, k % T, k.mod_lt h0, nat.mod_add_div' k T⟩,
  rw nat.modeq at h1 ⊢,
  rw [← nat.dvd_add_iff_left ⟨q, mul_comm q T⟩, pow_add, mul_comm q T, pow_mul,
      nat.mul_mod, nat.pow_mod (2 ^ T), h1, ← nat.pow_mod, one_pow, ← nat.mul_mod,
      mul_one, ← nat.modeq, nat.dvd_iff_mod_eq_zero, nat.mod_eq_of_lt h0, iff.comm],
  refine ⟨λ h2, _, λ h2, _⟩,
  rw [h2, pow_zero],
  contrapose! h0; exact nat.find_min' _ ⟨zero_lt_iff.mpr h0, h2⟩
end

lemma p_dvd_two_pow_sub_one_iff (k : ℕ) : p ∣ 2 ^ k - 1 ↔ order_two_mod_p h ∣ k :=
  by rw [← two_pow_mod_p_eq_one_iff, nat.modeq.comm,
         nat.modeq_iff_dvd' (nat.one_le_pow k 2 two_pos)]

lemma p_dvd_two_pow_order_two_mod_p : p ∣ 2 ^ order_two_mod_p h - 1 :=
  (p_dvd_two_pow_sub_one_iff h (order_two_mod_p h)).mpr (dvd_refl _)

lemma order_two_mod_p_dvd_totient : order_two_mod_p h ∣ p.totient :=
  (two_pow_mod_p_eq_one_iff h _).mp (nat.modeq.pow_totient (two_coprime_p h))

lemma order_two_even_of_neg_one_eq_two_pow (h0 : 1 < p) (h1 : ∃ c : ℕ, p ∣ 2 ^ c + 1) :
  even (order_two_mod_p h) :=
begin
  cases h1 with c h1,
  by_contra h2,
  replace h2 := (two_coprime_p (nat.odd_iff_not_even.mpr h2)).symm,
  have h3 : p ∣ (2 ^ c) ^ 2 - 1 ^ 2 :=
    by rw nat.sq_sub_sq; exact dvd_mul_of_dvd_left h1 (2 ^ c - 1),
  rw [one_pow, ← pow_mul, p_dvd_two_pow_sub_one_iff h,
      h2.dvd_mul_right, ← p_dvd_two_pow_sub_one_iff h] at h3,
  rw [← nat.sub_add_cancel (nat.one_le_pow c 2 two_pos),
      add_assoc, ← nat.dvd_add_iff_right h3, ← bit0] at h1,
  exact not_dvd_of_coprime (ne_of_gt h0) (two_coprime_p h) h1
end

theorem order_two_even_iff_prime_pow (h0 : is_prime_pow p) :
  even (order_two_mod_p h) ↔ ∃ c : ℕ, p ∣ 2 ^ c + 1 :=
begin
  ---- Right-to-left direction has been proved above
  rw is_prime_pow_nat_iff at h0,
  rcases h0 with ⟨q, k, hq, hk, rfl⟩,
  refine ⟨λ h0, _, order_two_even_of_neg_one_eq_two_pow h (nat.one_lt_pow k q hk hq.one_lt)⟩,
  cases h0 with c h0; rw ← mul_two at h0,
  have h1 : q ^ k ∣ (2 ^ c + 1) * (2 ^ c - 1) :=
    by rw [← nat.sq_sub_sq, one_pow, ← pow_mul, ← h0]; exact p_dvd_two_pow_order_two_mod_p h,
  refine ⟨c, (nat.coprime.dvd_mul_right (nat.coprime.pow_left _ _)).mp h1⟩,
  rw hq.coprime_iff_not_dvd,

  ---- Reduce to showing `q ∣ 2 ^ c + 1`
  suffices : q ∣ 2 ^ c + 1,
  { intros h2,
    rw [← nat.sub_add_cancel (nat.one_le_pow c 2 two_pos),
        add_assoc, ← nat.dvd_add_iff_right h2, ← bit0] at this,
    refine not_dvd_of_coprime hq.ne_one (two_coprime_p _) this,
    clear h0; contrapose h,
    rw [nat.odd_iff_not_even, not_not] at h ⊢,
    rw nat.even_pow; exact ⟨h, ne_of_gt hk⟩ },
  
  ---- Now show that `q ∣ 2 ^ c + 1`
  contrapose h1,
  rw ← hq.coprime_iff_not_dvd at h1,
  rw [(h1.pow_left k).dvd_mul_left, p_dvd_two_pow_sub_one_iff h, ← mul_one c, h0],
  replace h0 : 0 < c * 2 := by rw ← h0; exact order_two_mod_p_pos h,
  rw zero_lt_mul_right (nat.zero_lt_succ 1) at h0,
  rw [nat.mul_dvd_mul_iff_left h0, nat.dvd_one],
  norm_num
end

theorem order_two_even_iff_prime (hp : p.prime) :
  even (order_two_mod_p h) ↔ ∃ c : ℕ, p ∣ 2 ^ c + 1 :=
  order_two_even_iff_prime_pow h hp.is_prime_pow

end order_two



section properties

def F (p n : ℕ) := n + n % p
def S (p k n : ℕ) := (range k).sum (λ i, (2 ^ i * n) % p)

lemma F_mod_p (p n : ℕ) : F p n % p = (2 * n) % p :=
  by rw [F, nat.add_mod_mod, two_mul]

lemma F_iterate_mod_p (p k n : ℕ) : (F p^[k]) n % p = (2 ^ k * n) % p :=
begin
  induction k with k k_ih,
  rw [iterate_zero, id.def, pow_zero, one_mul],
  rw [iterate_succ', comp_app, F_mod_p, pow_succ, mul_assoc, nat.mul_mod, nat.mul_mod 2, k_ih]
end

lemma self_le_F (p n : ℕ) : n ≤ F p n :=
  le_self_add

lemma F_iterate_monotone (p n : ℕ) : monotone (λ i, (F p)^[i] n) :=
begin
  intros i j h,
  rw le_iff_exists_add at h,
  rcases h with ⟨c, rfl⟩,
  induction c with c c_ih,
  rw add_zero,
  rw nat.add_succ,
  simp_rw iterate_succ',
  exact le_trans c_ih (self_le_F p _)
end

lemma S_zero (p n : ℕ) : S p 0 n = 0 :=
  by rw [S, sum_range_zero]

lemma S_one (p n : ℕ) : S p 1 n = n % p :=
  by rw [S, sum_range_one, pow_zero, one_mul]

lemma S_succ (p k n : ℕ) : S p k.succ n = S p k n + (2 ^ k * n % p) :=
  sum_range_succ _ _

lemma S_succ' (p k n : ℕ) : S p k.succ n = S p k (2 * n) + n % p :=
begin
  rw [S, sum_range_succ', pow_zero, one_mul, add_left_inj, S],
  refine sum_congr rfl (λ x _, _),
  rw [pow_succ', mul_assoc]
end

lemma S_mod_p (p k n : ℕ) : S p k n = S p k (n % p) :=
begin
  induction k with k k_ih,
  rw [S_zero, S_zero],
  rw [S_succ, S_succ, ← k_ih, add_right_inj, eq_comm, nat.mul_mod, nat.mod_mod, ← nat.mul_mod]
end

lemma self_add_S_mod_p (p k n : ℕ) : (n + S p k n) % p = (2 ^ k * n) % p :=
begin
  induction k with k k_ih,
  rw [S_zero, add_zero, pow_zero, one_mul],
  rw [S_succ, ← add_assoc, ← nat.mod_add_mod, k_ih, ← nat.add_mod, ← two_mul, pow_succ, mul_assoc]
end

lemma F_iterate_S (p k n : ℕ) : (F p^[k]) n = n + S p k n :=
begin
  induction k with k k_ih,
  rw [iterate_zero, id.def, S_zero, add_zero],
  rw [iterate_succ', comp_app, k_ih, F, S_succ, ← add_assoc, self_add_S_mod_p]
end

lemma S_add_SS (p k k0 n : ℕ) : S p (k + k0) n = S p k n + S p k0 (2 ^ k * n) :=
begin
  rw [S, sum_range_add, S, add_right_inj, S],
  refine sum_congr rfl (λ x _, _),
  rw [add_comm, pow_add, mul_assoc]
end

lemma F_switch_sign {p a b : ℕ} (h0 : b < a) (h1 : F p a < F p b) :
  ∃ k x y : ℕ, p / 2 + x < y ∧ y < p ∧ a = x + (k + 1) * p ∧ b = y + k * p :=
begin
  ---- Throw out the case `p = 0`
  rw [F, F] at h1,
  rcases p.eq_zero_or_pos with rfl | h,
  rw [nat.mod_zero, ← two_mul, nat.mod_zero, ← two_mul] at h1,
  exfalso; exact lt_asymm h1 ((mul_lt_mul_left two_pos).mpr h0),

  ---- Rexpand `a = kp + x` and `b = mp + y`
  obtain ⟨m, x, h2, rfl⟩ : ∃ m x : ℕ, x < p ∧ x + m * p = a :=
    ⟨a / p, a % p, a.mod_lt h, a.mod_add_div' p⟩,
  obtain ⟨k, y, h3, rfl⟩ : ∃ k y : ℕ, y < p ∧ y + k * p = b :=
    ⟨b / p, b % p, b.mod_lt h, b.mod_add_div' p⟩,
  rw [nat.add_mul_mod_self_right, nat.mod_eq_of_lt h2, add_right_comm, ← two_mul,
      nat.add_mul_mod_self_right, nat.mod_eq_of_lt h3, add_right_comm, ← two_mul] at h1,
  
  ---- Reduce to showing that `m = k + 1`
  suffices h5 : m = k + 1,
  { subst h5; refine ⟨k, x, y, _, h3, rfl, rfl⟩,
    rw [add_comm k 1, one_add_mul, ← add_assoc, add_lt_add_iff_right] at h1,
    rwa [← nat.add_mul_div_right _ _ two_pos, add_comm,
         nat.div_lt_iff_lt_mul two_pos, mul_comm, mul_comm y] },

  ---- Finishing
  replace h2 : x < y :=
  begin
    rw [← add_lt_add_iff_left x, ← add_assoc, ← add_assoc, ← two_mul] at h0,
    replace h1 := lt_trans h0 h1,
    rwa [add_lt_add_iff_right, two_mul, add_lt_add_iff_right] at h1
  end,
  replace h0 := lt_trans (add_lt_add_right h2 _) h0,
  rw [add_lt_add_iff_left, mul_lt_mul_right h, lt_iff_exists_add] at h0,
  rcases h0 with ⟨c, h0, rfl⟩,
  rw [add_comm k, add_mul, ← add_assoc, add_lt_add_iff_right, two_mul y] at h1,
  replace h1 := lt_trans (lt_of_le_of_lt le_add_self h1) (add_lt_add h3 h3),
  rw [← two_mul, mul_lt_mul_right h, nat.lt_succ_iff] at h1,
  rw [gt_iff_lt, ← nat.succ_le_iff] at h0,
  rw le_antisymm h1 h0
end



variables {p : ℕ} (h : odd p)
include h

lemma F_injective : injective (F p) :=
begin
  intros x y h0,
  obtain ⟨q, q0, r, h1, rfl, rfl⟩ : ∃ q q0 r : ℕ, r < p ∧ q * p + r = x ∧ q0 * p + r = y :=
  begin
    refine ⟨x / p, y / p, x % p, x.mod_lt h.pos, nat.div_add_mod' x p, _⟩,
    convert nat.div_add_mod' y p using 2,
    replace h0 : (F p x) % p = (F p y) % p := congr_arg (λ c, c % p) h0,
    rw [F_mod_p, F_mod_p, ← nat.modeq] at h0,
    refine nat.modeq.cancel_left_of_coprime _ h0,
    rw [nat.odd_iff, ← nat.two_dvd_ne_zero] at h,
    rwa [← nat.coprime, nat.coprime_comm, nat.prime_two.coprime_iff_not_dvd]
  end,
  rw [F, F, nat.mul_add_mod, nat.mul_add_mod, add_left_inj, add_left_inj] at h0,
  rw h0
end

lemma F_coprime {n : ℕ} (h0 : n.coprime p) : (F p n).coprime p :=
begin
  rw [F, ← nat.coprime_add_mul_left_left _ _ (n / p), add_assoc, nat.mod_add_div, ← two_mul],
  exact (two_coprime_p h).mul h0
end


/-- Wrapper for `S_p(n)`, only up to length `T = ord_p(2)` -/
def S0 (n : ℕ) := S p (order_two_mod_p h) n

lemma F_iterate_coprime {n : ℕ} (h0 : n.coprime p) (N : ℕ) : (F p^[N] n).coprime p :=
begin
  induction N with N N_ih,
  rwa [iterate_zero, id.def],
  rw [iterate_succ', comp_app],
  exact F_coprime h N_ih
end

lemma S0_mod_p (n : ℕ) : S0 h n = S0 h (n % p) :=
  S_mod_p p _ n

lemma S0_two_mul (n : ℕ) : S0 h (2 * n) = S0 h n :=
begin
  have h0 := S_succ p (order_two_mod_p h) n,
  have h1 : 2 ^ order_two_mod_p h % p = 1 % p := two_pow_order_two_mod_p_eq_one h,
  rwa [S_succ', nat.mul_mod, h1, ← nat.mul_mod, one_mul, add_left_inj] at h0
end

lemma S0_two_pow_mul (n c : ℕ) : S0 h (2 ^ c * n) = S0 h n :=
begin
  induction c with c c_ih,
  rw [pow_zero, one_mul],
  rw [pow_succ, mul_assoc, S0_two_mul h, c_ih]
end

lemma S0_two_pow (c : ℕ) : S0 h (2 ^ c) = S0 h 1 :=
  by rw [← mul_one (2 ^ c), S0_two_pow_mul]

lemma S_mul_order (k n : ℕ) : S p (k * order_two_mod_p h) n = k * S0 h n :=
begin
  induction k with k k_ih,
  rw [zero_mul, S_zero, zero_mul],
  rw [nat.succ_mul, S_add_SS, k_ih, ← S0, S0_two_pow_mul h, nat.succ_mul]
end

lemma F_iterate_mul_ord (k n : ℕ) : (F p^[k * order_two_mod_p h]) n = n + k * S0 h n :=
  by rw [F_iterate_S, S_mul_order]

lemma S_mul_order_add (k n r : ℕ) :
  S p (k * order_two_mod_p h + r) n = k * S0 h n + S p r n :=
  by rw [add_comm, S_add_SS, S_mul_order h, S0_two_pow_mul h, add_comm]

lemma F_iterate_mul_ord_add (k n r : ℕ) :
  (F p^[k * order_two_mod_p h + r]) n = n + k * S0 h n + S p r n :=
  by rw [F_iterate_S, S_mul_order_add, add_assoc]

lemma S0_F_iterate (k n : ℕ) : S0 h (F p^[k] n) = S0 h n :=
  by rw [S0_mod_p h, F_iterate_mod_p, ← S0_mod_p h, S0_two_pow_mul]

lemma S_p_dvd_add {m n : ℕ} (h0 : ¬p ∣ m) (h1 : p ∣ m + n) (k : ℕ) :
  S p k m + S p k n = k * p :=
begin
  revert h0 h1 m n,
  induction k with k k_ih; intros m n h0 h1,
  rw [S_zero, S_zero, add_zero, zero_mul],
  rw [S_succ', S_succ', add_add_add_comm, k_ih, nat.succ_mul, add_right_inj],
  have X := nat.le_mod_add_mod_of_dvd_add_of_not_dvd h1 h0,
  replace X := nat.add_mod_add_of_le_add_mod X,
  rwa [nat.mod_eq_zero_of_dvd h1, zero_add, eq_comm] at X,
  rwa (two_coprime_p h).symm.dvd_mul_left,
  rw ← mul_add; exact dvd_mul_of_dvd_right h1 2
end

lemma S0_p_dvd_add {m n : ℕ} (h0 : ¬p ∣ m) (h1 : p ∣ m + n) :
  S0 h m + S0 h n = order_two_mod_p h * p :=
  S_p_dvd_add h h0 h1 (order_two_mod_p h)

lemma eventually_F_lt_of_S0_lt {a b : ℕ} (h0 : S0 h a < S0 h b) :
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (F p^[n]) a < (F p^[n]) b :=
begin
  ---- Find `K` large enough
  obtain ⟨K, h1⟩ : ∃ K : ℕ, a + (K + 1) * S0 h a < b + K * S0 h b :=
  begin
    generalize_hyp : S0 h a = c at h0 ⊢,
    generalize_hyp : S0 h b = d at h0 ⊢,
    use a + c + 1,
    rw [add_one_mul, add_left_comm, ← nat.add_one_le_iff, add_assoc, ← mul_add_one],
    rw ← nat.add_one_le_iff at h0,
    exact le_trans (mul_le_mul_left' h0 (a + c + 1)) le_add_self
  end,

  ---- Pick `N = kT`, and if `n = kT + r`, reduce to `a + (k + 1) S_p(a) < b + k S_p(b)`
  let T := order_two_mod_p h,
  have hT : 0 < T := order_two_mod_p_pos h,
  refine ⟨K * T, λ n hn, _⟩,
  obtain ⟨k, r, h2, rfl⟩ : ∃ k r : ℕ, r < T ∧ k * T + r = n :=
    ⟨n / T, n % T, n.mod_lt hT, nat.div_add_mod' n T⟩,
  refine lt_of_lt_of_le _ (F_iterate_monotone p b le_self_add),
  refine lt_of_le_of_lt (F_iterate_monotone p a (add_le_add_left (le_of_lt h2) _)) _,
  simp only []; rw [← add_one_mul, F_iterate_S, S_mul_order h, F_iterate_S, S_mul_order h],

  ---- Prove that `a + (k + 1) S_p(a) < b + k S_p(b)`
  replace hn : (K * T) / T ≤ (k * T + r) / T := nat.div_le_div_right hn,
  rw [nat.mul_div_cancel _ hT, add_comm, nat.add_mul_div_right _ _ hT,
      nat.div_eq_zero h2, zero_add, le_iff_exists_add] at hn,
  rcases hn with ⟨c, rfl⟩,
  rw [add_right_comm, add_mul, add_mul K c, ← add_assoc, ← add_assoc],
  exact add_lt_add_of_lt_of_le h1 (mul_le_mul_left' (le_of_lt h0) c)
end

end properties



section Mersenne

/-- This lemma proves that the Mersenne numbers `2^k - 1` are odd for `k > 0`.
  For the rest of the lemmas, we use the oddness of `2^k - 1` as the hypothesis itself. -/
lemma Mersenne_odd {k : ℕ} (h : 0 < k) : odd (2 ^ k - 1) :=
begin
  rw [nat.odd_iff_not_even, ← nat.even_add_one,
      nat.sub_add_cancel (nat.one_le_pow k 2 two_pos), nat.even_pow' (ne_of_gt h)],
  exact even_two
end

variables {k : ℕ} (h : odd (2 ^ k - 1))
include h

lemma order_two_mod_Mersenne : order_two_mod_p h = k :=
begin
  have X : ∀ m : ℕ, 1 ≤ 2 ^ m := λ m, nat.one_le_pow m 2 two_pos,
  unfold order_two_mod_p; apply le_antisymm,
  rw nat.find_le_iff; refine ⟨k, le_refl k, _, nat.modeq_sub (X k)⟩,
  rw zero_lt_iff; rintros rfl,
  rw [pow_zero, nat.sub_self, nat.odd_iff_not_even] at h,
  exact h even_zero,
  rw nat.le_find_iff; rintros m h0 ⟨h1, h2⟩,
  rw [nat.modeq.comm, nat.modeq_iff_dvd' (X m)] at h2,
  revert h2; refine nat.not_dvd_of_pos_of_lt _ _,
  rw tsub_pos_iff_lt; exact nat.one_lt_pow m 2 h1 one_lt_two,
  rw tsub_lt_tsub_iff_right (X m); exact pow_lt_pow one_lt_two h0
end

lemma S0_Mersenne_one (h0 : 1 < k) : S0 h 1 = 2 ^ k - 1 :=
begin
  conv_rhs { rw ← geom_sum_mul_add 1 k },
  rw [S0, order_two_mod_Mersenne, S, nat.add_sub_cancel, mul_one],
  refine sum_congr rfl (λ i h1, _),
  rw [mul_one, nat.mod_eq_of_lt],
  obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero (ne_of_gt (lt_trans one_pos h0)),
  rw [mem_range, nat.lt_succ_iff] at h1,
  rw [lt_tsub_iff_right, pow_succ, two_mul],
  refine add_lt_add_of_le_of_lt (nat.pow_le_pow_of_le_right two_pos h1) _,
  rw nat.succ_lt_succ_iff at h0; exact nat.one_lt_two_pow m h0
end

lemma S0_Mersenne_neg_two_pow (h0 : 1 < k) {m : ℕ} (h1 : m < k) :
  S0 h (2 ^ k - 1 - 2 ^ m) = (k - 1) * (2 ^ k - 1) :=
begin
  have h2 := two_pow_lt_Mersenne h0 h1,
  rw [← add_right_inj (S0 h (2 ^ m)), S0_p_dvd_add, order_two_mod_Mersenne, add_comm,
      S0_two_pow h, S0_Mersenne_one h h0, ← add_one_mul, nat.sub_add_cancel (le_of_lt h0)],
  exact nat.not_dvd_of_pos_of_lt (pow_pos two_pos m) h2,
  rw [add_comm, nat.sub_add_cancel (le_of_lt h2)]
end

lemma S0_Mersenne_neg_one (h0 : 1 < k) : S0 h (2 ^ k - 1 - 1) = (k - 1) * (2 ^ k - 1) :=
  S0_Mersenne_neg_two_pow h h0 (lt_trans one_pos h0)

end Mersenne

end IMO2020N4
end IMOSL
