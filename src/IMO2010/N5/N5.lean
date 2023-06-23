import number_theory.padics.padic_val data.nat.parity

/-! # IMO 2010 N5 (P3) -/

namespace IMOSL
namespace IMO2010N5

def good (f : ℕ → ℕ) (c : ℕ) := ∀ m n : ℕ, is_square ((f m + n + c) * (f n + m + c))



lemma padic_val_mul_of_not_dvd_right {p : ℕ} [fact p.prime] (x : ℕ) {y : ℕ} (h : ¬p ∣ y) :
  padic_val_nat p (x * y) = padic_val_nat p x :=
  (eq_or_ne x 0).elim (λ h0, congr_arg (padic_val_nat p) $ by rw [h0, zero_mul]) $
    λ h0, (padic_val_nat.mul h0 $ λ h1, h ⟨0, h1.trans (mul_zero p).symm⟩).trans $
      by rw [padic_val_nat.eq_zero_of_not_dvd h, add_zero]

lemma padic_val_pow {p : ℕ} [fact p.prime] (a n : ℕ) :
  padic_val_nat p (a ^ n) = n * padic_val_nat p a :=
  (ne_or_eq a 0).elim (padic_val_nat.pow n) $ λ h0, n.eq_zero_or_pos.elim
    (λ h1, by rw [h1, zero_mul, pow_zero, padic_val_nat.one])
    (λ h1, by rw [h0, zero_pow h1, padic_val_nat.zero, mul_zero])

lemma p_dvd_of_is_square_mul_padic_val_bit1 {p : ℕ} (h : p.prime) {x y : ℕ} (n : ℕ)
  (h0 : is_square (x * y)) (h1 : p ^ bit1 n ∣ x ∧ ¬p ^ (bit1 n).succ ∣ x) : p ∣ y :=
begin
  rcases h1 with ⟨⟨m, rfl⟩, h2⟩,
  rw [pow_succ', nat.mul_dvd_mul_iff_left (pow_pos h.pos _)] at h2,
  cases h0 with k h0,
  by_contra h1,
  replace h0 := congr_arg (padic_val_nat p) h0,
  haveI : fact p.prime := ⟨h⟩,
  rw [← sq, padic_val_pow, padic_val_mul_of_not_dvd_right _ h1, two_mul,
      padic_val_mul_of_not_dvd_right _ h2, padic_val_nat.prime_pow] at h0,
  exact n.not_even_bit1 ⟨padic_val_nat p k, h0⟩
end

lemma exists_le_padic_val_eq {p : ℕ} (h : p.prime) (x n : ℕ) :
  ∃ y : ℕ, x ≤ y ∧ p ^ n ∣ y ∧ ¬p ^ (n + 1) ∣ y :=
  ⟨p ^ n * (p * x + 1),
  by rw [mul_add_one, ← mul_assoc, ← pow_succ'];
    exact (nat.le_mul_of_pos_left $ pow_pos h.pos n.succ).trans le_self_add,
  ⟨p * x + 1, rfl⟩,
  by rw [pow_succ', nat.mul_dvd_mul_iff_left (pow_pos h.pos n), nat.dvd_add_right ⟨x, rfl⟩]; 
    exact h.not_dvd_one⟩





lemma add_is_good (c k : ℕ) : good (has_add.add k) c :=
  λ m n, ⟨k + m + n + c, congr_arg (has_mul.mul _) $ congr_arg (+ c) (add_right_comm k n m)⟩



section good_lemmas

variables {f : ℕ → ℕ} {c : ℕ} (h : good f c)
include h

lemma good_imp_mod_prime_compat {p : ℕ} (h0 : p.prime) {x y : ℕ} (h1 : f x ≡ f y [MOD p]) :
  x ≡ y [MOD p] :=
begin
  by_cases h2 : f x ≡ f y [MOD p ^ 2],

  ---- Case 1: `f(x) ≡ f(y) (mod p^2)`
  { rcases exists_le_padic_val_eq h0 (f x + c) 1 with ⟨z, h3, h4⟩,
    rw le_iff_exists_add at h3; rcases h3 with ⟨k, rfl⟩,
    refine nat.modeq.add_right_cancel' (f k + c) _,
    
    rw add_right_comm at h4,
    rw [add_left_comm, ← add_assoc, add_left_comm, ← add_assoc, nat.modeq, eq_comm,
        nat.dvd_iff_mod_eq_zero.mp (p_dvd_of_is_square_mul_padic_val_bit1 h0 0 (h x k) h4)],
    refine nat.dvd_iff_mod_eq_zero.mp (p_dvd_of_is_square_mul_padic_val_bit1 h0 0 (h y k) _),
    rw [nat.dvd_iff_mod_eq_zero, nat.dvd_iff_mod_eq_zero, add_assoc, pow_one] at h4 ⊢,
    revert h4; exact and.imp (eq.trans $ h1.symm.add_right _)
      (ne_of_eq_of_ne $ h2.symm.add_right _) },

  ---- Case 2: `¬f(x) ≡ f(y) (mod p^2)`
  { rcases exists_le_padic_val_eq h0 (f x + c) 3 with ⟨z, h3, h4⟩,
    rw le_iff_exists_add at h3; rcases h3 with ⟨k, rfl⟩,
    refine nat.modeq.add_right_cancel' (f k + c) _,
    
    rw add_right_comm at h4,
    rw [add_left_comm, ← add_assoc, add_left_comm, ← add_assoc, nat.modeq, eq_comm,
        nat.dvd_iff_mod_eq_zero.mp (p_dvd_of_is_square_mul_padic_val_bit1 h0 _ (h x k) h4)],
    refine nat.dvd_iff_mod_eq_zero.mp (p_dvd_of_is_square_mul_padic_val_bit1 h0 0 (h y k) ⟨_, _⟩),

    { replace h4 := (pow_dvd_pow p $ nat.succ_pos 2).trans h4.1,
      rw [pow_one, nat.dvd_iff_mod_eq_zero, add_assoc] at h4 ⊢,
      rw ← h4; exact h1.symm.add_right _ },

    { replace h4 := (pow_dvd_pow p $ nat.le_succ 2).trans h4.1,
      rw [nat.dvd_iff_mod_eq_zero, add_assoc] at h4 ⊢,
      intros h3; exact h2 (nat.modeq.add_right_cancel' (k + c) $ h4.trans h3.symm) } }
end

lemma good_inj : function.injective f :=
begin
  intros x y h0,
  obtain ⟨p, h1, h2⟩ := (max x y).succ.exists_infinite_primes,
  replace h2 : x % p = y % p := good_imp_mod_prime_compat h h2 (congr_arg (% p) h0),
  rw [nat.succ_le_iff, max_lt_iff] at h1,
  rwa [nat.mod_eq_of_lt h1.1, nat.mod_eq_of_lt h1.2] at h2
end

lemma good_map_add_one (x : ℕ) : f (x + 1) = f x + 1 ∨ f x = f (x + 1) + 1 :=
  (le_total (f x) (f x.succ)).imp
    (λ h0, begin
      rw le_iff_exists_add at h0,
      cases h0 with t h0,
      rw [h0, add_right_inj, nat.eq_one_iff_not_exists_prime_dvd],
      rintros p h1 ⟨r, rfl⟩,
      replace h0 : f x.succ % p = (f x + p * r) % p := congr_arg (% p) h0,
      rw nat.add_mul_mod_self_left at h0,
      replace h0 := (good_imp_mod_prime_compat h h1 h0).symm,
      rw [nat.modeq_iff_dvd' x.le_succ, nat.succ_eq_add_one,
          nat.add_sub_cancel_left] at h0,
      exact h1.not_dvd_one h0
    end)
    (λ h0, begin
      rw le_iff_exists_add at h0,
      cases h0 with t h0,
      rw [h0, add_right_inj, nat.eq_one_iff_not_exists_prime_dvd],
      rintros p h1 ⟨r, rfl⟩,
      replace h0 : f x % p = (f x.succ + p * r) % p := congr_arg (% p) h0,
      rw nat.add_mul_mod_self_left at h0,
      replace h0 := good_imp_mod_prime_compat h h1 h0,
      rw [nat.modeq_iff_dvd' x.le_succ, nat.succ_eq_add_one,
          nat.add_sub_cancel_left] at h0,
      exact h1.not_dvd_one h0
    end)

lemma good_map_antitone_aux {x : ℕ} (h0 : f x = f (x + 1) + 1) :
  f (x + 1) = f (x + 2) + 1 :=
  (good_map_add_one h x.succ).symm.elim id $
    λ h1, absurd (good_inj h $ h0.trans h1.symm) $
      ne_of_lt $ nat.lt_add_right x x.succ 1 x.lt_succ_self

lemma good_map_antitone_aux2 {x : ℕ} (h0 : f x = f (x + 1) + 1) :
  ∀ n : ℕ, f (x + n) = f (x + n.succ) + 1
| 0 := h0
| (n+1) := good_map_antitone_aux h $ good_map_antitone_aux2 n

lemma good_map_antitone_aux3 {x : ℕ} (h0 : f x = f (x + 1) + 1) :
  ∀ n : ℕ, f x = f (x + n) + n
| 0 := rfl
| (n+1) := (good_map_antitone_aux3 n).trans $
    (congr_arg (+ n) (good_map_antitone_aux2 h h0 n)).trans $
      (add_right_comm _ _ _).trans $ add_assoc _ _ _

lemma good_map_monotone (x : ℕ) : f (x + 1) = f x + 1 :=
  (good_map_add_one h x).elim id $ λ h0, absurd (good_map_antitone_aux3 h h0 (f x).succ) $
    ne_of_lt $ nat.lt_add_left _ (f x).succ _ (f x).lt_succ_self

lemma good_map_eq_has_add : ∀ n, f n = f 0 + n
| 0 := rfl
| (n+1) := by rw [good_map_monotone h, good_map_eq_has_add, add_assoc]

end good_lemmas





/-- Final solution -/
theorem final_solution {f : ℕ → ℕ} {c : ℕ} : good f c ↔ ∃ k : ℕ, f = has_add.add k :=
  ⟨λ h, ⟨f 0, funext $ good_map_eq_has_add h⟩,
    λ h, exists.elim h $ λ k h0, by rw h0; exact add_is_good c k⟩

end IMO2010N5
end IMOSL
