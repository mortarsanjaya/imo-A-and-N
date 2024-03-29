import data.nat.factorization.basic data.zmod.basic

/-!
# Representation of the coprime part of a `nat` in `zmod`

Given a positive integer `n = p^k t`, where `p` is prime, `k ≥ 0` and `t` is coprime with `p`,
  we define `zmod.ord_compl p n` as the image of `t` in `(zmod p)ˣ`.
We also prove some important properties of `zmod.ord_compl`

Some important properties on a positive integer can be evaluated just by
  analyzing the value of `k` and the image `u` of `t` in `(zmod p)ˣ`.
For example, `n` is a square in `ℤ_p`, `p ≠ 2` if and only if `k` is even and `u` is a square.
-/



namespace IMOSL
namespace extra
namespace zmod

@[simp] lemma unit_of_coprime_one {p : ℕ} [fact p.prime] (h0 : nat.coprime 1 p) :
  zmod.unit_of_coprime 1 h0 = 1 :=
  by rw zmod.unit_of_coprime;
    conv_lhs { congr, rw nat.cast_one, skip, rw [nat.cast_one, inv_one] }; refl



/-- The `p`-coprime part of a positive natural, embedded into `(zmod p)ˣ`.
  If `n = 0`, we define the `p`-coprime part to be `1` in `(zmod p)ˣ`. -/
def ord_compl (p : ℕ) [fact (p.prime)] (n : ℕ) : (zmod p)ˣ :=
  dite (n = 0) (λ _, 1) (λ h : n ≠ 0, zmod.unit_of_coprime (ord_compl[p] n)
    (nat.coprime_comm.mp (nat.coprime_ord_compl (fact.out p.prime) h)))

namespace ord_compl

variables {p : ℕ} [fact (p.prime)]

@[simp] theorem map_zero : ord_compl p 0 = 1 :=
  by rw [ord_compl, dif_pos rfl]

@[simp] theorem map_ne_zero_zmod {n : ℕ} (h : n ≠ 0) :
  (zmod.ord_compl p n : zmod p) = ((ord_compl[p] n : ℕ) : zmod p) :=
  by rw [ord_compl, dif_neg h, zmod.coe_unit_of_coprime]

theorem map_ne_zero_val {n : ℕ} (h : n ≠ 0) :
  (zmod.ord_compl p n : zmod p).val = ord_compl[p] n % p :=
  by rw [map_ne_zero_zmod h, zmod.val_nat_cast]

@[simp] theorem map_one : ord_compl p 1 = 1 :=
begin
  rw [ord_compl, dif_neg nat.one_ne_zero],
  conv_lhs { congr, rw [nat.factorization_one, finsupp.coe_zero,
    pi.zero_apply, pow_zero, nat.div_one] },
  exact unit_of_coprime_one _
end

@[simp] theorem map_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
  ord_compl p (m * n) = ord_compl p m * ord_compl p n :=
  by rw [← units.eq_iff, map_ne_zero_zmod (nat.mul_ne_zero hm hn), units.coe_mul,
    map_ne_zero_zmod hm, map_ne_zero_zmod hn, nat.ord_compl_mul, nat.cast_mul]

@[simp] theorem map_pow : ∀ m k : ℕ, ord_compl p (m ^ k) = ord_compl p m ^ k
| _ 0 := by rw [pow_zero, map_one, pow_zero]
| 0 (k+1) := by rw [zero_pow k.succ_pos, map_zero, one_pow]
| (m+1) (k+1) := by rw [pow_succ, pow_succ, ← map_pow,
  map_mul m.succ_ne_zero (pow_ne_zero _ m.succ_ne_zero), map_pow]

@[simp] lemma map_self : ord_compl p p = 1 :=
  by have h := fact.out p.prime; rw [← units.coe_eq_one, map_ne_zero_zmod h.ne_zero,
    h.factorization_self, pow_one, nat.div_self h.pos, nat.cast_one]

@[simp] lemma map_self_pow (k : ℕ) : ord_compl p (p ^ k) = 1 :=
  by rw [map_pow, map_self, one_pow]

@[simp] lemma map_self_pow_mul (k n : ℕ) : ord_compl p (p ^ k * n) = ord_compl p n :=
begin
  rcases eq_or_ne n 0 with rfl | h,
  rw mul_zero,
  rw [map_mul (pow_ne_zero _ (fact.out p.prime).ne_zero) h, map_self_pow, one_mul]
end

lemma map_coprime {t : ℕ} (h : t.coprime p) : ord_compl p t = zmod.unit_of_coprime t h :=
begin
  have hp := fact.out p.prime,
  have h0 : ¬p ∣ t := by rwa [← nat.prime.coprime_iff_not_dvd hp, nat.coprime_comm],
  rw units.ext_iff; apply zmod.val_injective,
  rw [map_ne_zero_val, zmod.coe_unit_of_coprime, nat.factorization_def t hp,
      padic_val_nat.eq_zero_of_not_dvd h0, pow_zero, nat.div_one, zmod.val_nat_cast],
  rintros rfl; exact h0 (dvd_zero p)
end

lemma map_coprime_val {t : ℕ} (h : t.coprime p) : (ord_compl p t : zmod p).val = t % p :=
  by rw [map_coprime h, zmod.coe_unit_of_coprime, zmod.val_nat_cast]

lemma map_zmod_unit_val (x : (zmod p)ˣ) : ord_compl p (x : zmod p).val = x :=
  by rw [units.ext_iff, map_coprime (zmod.val_coe_unit_coprime x),
    zmod.coe_unit_of_coprime, zmod.nat_cast_val, zmod.cast_id', id.def]

lemma map_coprime_mod_p {t : ℕ} (h : t.coprime p) : ord_compl p t = ord_compl p (t % p) :=
begin
  refine units.ext (zmod.val_injective p _),
  rw [map_coprime_val h, map_coprime_val, nat.mod_mod],
  rw nat.coprime at h ⊢,
  rw ← h; apply nat.modeq.gcd_eq,
  rw [nat.modeq, nat.mod_mod]
end

lemma map_coprime_p_dvd_add {a b : ℕ} (h : a.coprime p) (h0 : p ∣ a + b) :
  ord_compl p b = -ord_compl p a :=
begin
  rwa [units.ext_iff, units.coe_neg, map_coprime h, zmod.coe_unit_of_coprime,
       map_coprime, zmod.coe_unit_of_coprime, eq_neg_iff_add_eq_zero,
       ← nat.cast_add, zmod.nat_coe_zmod_eq_zero_iff_dvd, add_comm],
  rw [nat.coprime_comm, (fact.out p.prime).coprime_iff_not_dvd] at h ⊢,
  intros h1; exact h ((nat.dvd_add_left h1).mp h0)
end

end ord_compl

end zmod
end extra
end IMOSL