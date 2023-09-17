import data.nat.prime_fin data.nat.modeq data.pnat.basic

/-! # IMO 2019 N4 -/

namespace IMOSL
namespace IMO2019N4

/- ### Extra lemmas -/

lemma sq_mod_eq_of_dvd_add {a b c : ℕ} (h : c ∣ a + b) : a ^ 2 ≡ b ^ 2 [MOD c] :=
  nat.modeq.add_left_cancel' (a * b) $ by rw [sq, ← mul_add, add_comm, sq, ← add_mul];
    exact (nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_right h _).trans
      (nat.mod_eq_zero_of_dvd $ dvd_mul_of_dvd_left h _).symm

lemma dvd_sq_iff_dvd_sq_of_dvd_add {a b c : ℕ} (h : c ∣ a + b) : c ∣ a ^ 2 ↔ c ∣ b ^ 2 :=
  by rw [nat.dvd_iff_mod_eq_zero, nat.dvd_iff_mod_eq_zero];
    exact eq.congr (sq_mod_eq_of_dvd_add h) rfl

lemma eq_zero_of_prime_add_dvd_sq {p a : ℕ} (h : p.prime)
  (h0 : a < p) (h1 : p + a ∣ p ^ 2) : a = 0 :=
begin
  rw nat.dvd_prime_pow h at h1,
  rcases h1 with ⟨k, h1, h2⟩,
  rw [nat.le_add_one_iff, nat.le_add_one_iff, zero_add, le_zero_iff] at h1,
  rcases h1 with (rfl | rfl) | rfl,
  -- `p + a = 1`
  exact absurd h2 (ne_of_gt $ h.one_lt.trans_le le_self_add),
  -- `p + a = p`
  rwa [pow_one, add_right_eq_self] at h2,
  -- `p + a = p^2`
  refine absurd h2 (ne_of_lt $ (add_lt_add_left h0 p).trans_le _),
  rw [sq, ← two_mul],
  exact nat.mul_le_mul_right p h.two_le
end





/- ### Start of the problem -/

def good (C : ℕ) (f : ℕ → ℕ) := ∀ a b : ℕ, C < a + b → a + f b ∣ a ^ 2 + b * f a



lemma linear_is_good (C k : ℕ) : good C (has_mul.mul k) :=
  λ a b _, ⟨a, by rw [sq, add_mul, mul_assoc, mul_left_comm]⟩

section results

variables {C : ℕ} {f : ℕ → ℕ} (h : good C f)
include h

lemma good_upper_bound {b : ℕ} (h0 : C ≤ b) : f b ≤ f 1 * b :=
  (nat.le_of_add_le_add_left $ nat.le_of_dvd (nat.add_pos_left nat.one_pos _)
    (h 1 b $ nat.lt_one_add_iff.mpr h0)).trans_eq (mul_comm b $ f 1)

lemma self_dvd_f_sq {b : ℕ} (h0 : 0 < b) : b ∣ f b ^ 2 :=
begin
  cases exists_gt (C + f b) with n h1,
  replace h1 : C + f b < n * b := h1.trans_le (nat.le_mul_of_pos_right h0),
  cases nat.exists_eq_add_of_le (le_of_lt h1) with a0 h2,
  rw add_right_comm at h2,
  replace h2 : b ∣ C + a0 + f b := ⟨n, h2.symm.trans (mul_comm n b)⟩,
  replace h := dvd_trans h2 (h (C + a0) b (lt_add_of_le_of_pos le_self_add h0)),
  rwa [← nat.dvd_add_iff_left (dvd_mul_right b _), dvd_sq_iff_dvd_sq_of_dvd_add h2] at h
end

lemma self_dvd_f_of_prime {p : ℕ} (h0 : p.prime) : p ∣ f p :=
  h0.dvd_of_dvd_pow (self_dvd_f_sq h h0.pos)

lemma f_prime_large {p : ℕ} (h0 : p.prime) (h1 : C ≤ p) (h2 : f 1 < p) : f p = f 1 * p :=
begin
  cases self_dvd_f_of_prime h h0 with k h3,
  rcases k.eq_zero_or_pos with rfl | h4,

  ---- `k = 0`
  { rw mul_zero at h3,
    have h4 := h p 1 (nat.lt_succ_iff.mpr h1),
    rw [one_mul, h3, add_zero] at h4,
    rw [h3, eq_zero_of_prime_add_dvd_sq h0 h2 h4, zero_mul] },

  ---- `k > 0`
  { rw [h3, mul_comm, mul_eq_mul_right_iff, or_iff_left h0.ne_zero],
    have h5 := good_upper_bound h h1,
    rw [h3, mul_comm, mul_le_mul_right h0.pos, le_iff_exists_add] at h5,
    cases h5 with c h5,
    have h6 := h 1 p (nat.lt_one_add_iff.mpr h1),
    rw [h3, h5, one_pow, mul_add, ← add_assoc, nat.dvd_add_self_left,
      ((nat.coprime_add_mul_left_left 1 p k).mpr $ nat.coprime_one_left p).dvd_mul_left] at h6,
    rw [h5, self_eq_add_right],
    exact nat.eq_zero_of_dvd_of_lt h6 (nat.lt_one_add_iff.mpr $ le_add_self.trans $
      h5.symm.trans_le $ (le_of_lt h2).trans $ nat.le_mul_of_pos_right h4) }
end

lemma f_is_linear (n : ℕ) : f n = f 1 * n :=
n.eq_zero_or_pos.elim
---- `n = 0`
(λ h0, begin
  rw [h0, mul_zero],
  rcases nat.exists_infinite_primes (max C (f 0)).succ with ⟨p, h1, h2⟩,
  rw [nat.succ_le_iff, max_lt_iff] at h1,
  refine eq_zero_of_prime_add_dvd_sq h2 h1.2 ((h p 0 h1.1).trans $ dvd_of_eq _),
  rw [zero_mul, add_zero]
end) $
---- `f(1) = 0`
(f 1).eq_zero_or_pos.elim
(λ h0 h1, begin
  rw [h0, zero_mul],
  rcases nat.exists_infinite_primes (max C (f n)).succ with ⟨p, h1, h2⟩,
  rw [nat.succ_le_iff, max_lt_iff] at h1,
  refine eq_zero_of_prime_add_dvd_sq h2 h1.2
    ((h p n $ h1.1.trans_le le_self_add).trans $ dvd_of_eq _),
  rw [f_prime_large h h2 (le_of_lt h1.1) (h0.trans_lt h2.pos), h0, zero_mul, mul_zero, add_zero]
end)
---- `f(1) > 0`
(λ h0 h1, begin
  rcases nat.exists_infinite_primes (max C $ max (f n) (f 1 * n)).succ with ⟨p, h2, h3⟩,
  rw [nat.succ_le_iff, max_lt_iff, max_lt_iff] at h2,
  have h4 : p ≤ n + f 1 * p := (nat.le_mul_of_pos_left h0).trans le_add_self,
  refine nat.modeq.eq_of_lt_of_lt _ (h2.2.1.trans_le h4) (h2.2.2.trans_le h4),
  replace h4 : (n + f 1 * p).gcd p = 1 := (nat.gcd_add_mul_right_left _ _ _).trans
    (nat.coprime_of_lt_prime h1 ((nat.le_mul_of_pos_left h0).trans_lt h2.2.2) h3).symm,
  refine (nat.modeq.add_left_cancel' (n ^ 2) _).cancel_right_of_coprime h4,
  replace h4 := f_prime_large h h3 (le_of_lt h2.1) ((nat.le_mul_of_pos_right h1).trans_lt h2.2.2),
  rw [nat.modeq, mul_comm, ← h4, nat.mod_eq_zero_of_dvd (h n p $ h2.1.trans_le le_add_self),
      sq, mul_right_comm, ← add_mul, ← h4, eq_comm],
  exact nat.mod_eq_zero_of_dvd ⟨n, rfl⟩
end)

end results



/-- Final solution -/
theorem final_solution {C : ℕ} {f : ℕ → ℕ} : good C f ↔ ∃ k : ℕ, f = has_mul.mul k :=
⟨λ h, ⟨f 1, funext $ f_is_linear h⟩,
λ h, exists.elim h $ λ k h, h.symm ▸ linear_is_good C k⟩







/- ### Extension from `ℕ+ → ℕ+` to `ℕ → ℕ` -/

/-- Extension of a function `ℕ+ → ℕ+` to a function `ℕ → ℕ` -/
def pnat_fun_extension (f : ℕ+ → ℕ+) : ℕ → ℕ :=
  λ n : ℕ, dite (0 < n) (λ h, f ⟨n, h⟩) (λ _, 0)

lemma pnat_fun_extension_zero (f : ℕ+ → ℕ+) : pnat_fun_extension f 0 = 0 := 
  rfl

lemma pnat_fun_extension_pos (f : ℕ+ → ℕ+) {n : ℕ} (h : 0 < n) :
  pnat_fun_extension f n = f ⟨n, h⟩ :=
  dif_pos h

lemma pnat_fun_extension_pnat (f : ℕ+ → ℕ+) (n : ℕ+) : pnat_fun_extension f n = f n :=
  (dif_pos n.2).trans $ congr_arg coe $ congr_arg f $ subtype.coe_eta n n.2





/- ### Original version with `ℕ+` -/

def pnat_good (C : ℕ+) (f : ℕ+ → ℕ+) := ∀ a b : ℕ+, C < a + b → a + f b ∣ a ^ 2 + b * f a

lemma pnat_linear_is_good (C k : ℕ+) : pnat_good C (has_mul.mul k) :=
  λ a b _, ⟨a, by rw [sq, add_mul, mul_assoc, mul_left_comm]⟩

lemma pnat_good_imp_good {C : ℕ+} {f : ℕ+ → ℕ+} (h : pnat_good C f) :
  good C (pnat_fun_extension f) :=
  λ a b h0, a.eq_zero_or_pos.elim (λ h1, by rw [h1, zero_pow (nat.succ_pos 1),
    pnat_fun_extension_zero, zero_add, zero_add, mul_zero]; exact dvd_zero _) $
  λ h1, b.eq_zero_or_pos.elim (λ h2, by rw [h2, pnat_fun_extension_zero,
    add_zero, zero_mul, add_zero]; exact dvd_pow_self a (nat.succ_ne_zero 1)) $
  λ h2, begin
    rw [pnat_fun_extension_pos f h2, pnat_fun_extension_pos f h1],
    have h3 := h ⟨a, h1⟩ ⟨b, h2⟩ h0,
    rwa [pnat.dvd_iff, pnat.add_coe, pnat.add_coe, pnat.pow_coe,
         pnat.mul_coe, pnat.mk_coe, pnat.mk_coe] at h3
  end

lemma pnat_good_imp_linear {C : ℕ+} {f : ℕ+ → ℕ+} (h : pnat_good C f) (n : ℕ+) :
  f n = f 1 * n :=
  have _, from f_is_linear (pnat_good_imp_good h) n,
  by rwa [pnat_fun_extension_pnat, ← pnat.one_coe,
    pnat_fun_extension_pnat, ← pnat.mul_coe, pnat.coe_inj] at this





/-- Final solution, `ℕ+` version -/
theorem final_solution_pnat {C : ℕ+} {f : ℕ+ → ℕ+} :
  (∀ a b : ℕ+, C < a + b → a + f b ∣ a ^ 2 + b * f a) ↔ ∃ k : ℕ+, f = has_mul.mul k :=
⟨λ h, ⟨f 1, funext $ pnat_good_imp_linear h⟩,
λ h, exists.elim h $ λ k h, h.symm ▸ pnat_linear_is_good C k⟩

end IMO2019N4
end IMOSL
