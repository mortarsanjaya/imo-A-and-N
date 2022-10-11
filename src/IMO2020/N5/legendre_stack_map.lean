import IMO2020.N5.additive_map number_theory.legendre_symbol.jacobi_symbol

/-!
# "Legendre stack" maps

Let `p : ℕ → ℕ := p_0 < p_1 < p_2 < ...` be an ascending chain of primes.
We call it a **Legendre stack** if `p_{n + 1} ≡ p_n (mod 4(p_n - 1)!)` for all `n ≥ 0`.
We prove one important property related to the Legendre stack:
* For any `m : ℤ` and `j k : ℕ` with `|m| < min{p_j, p_k}`, we have `(m | p_j) = (m | p_k)`.
Here, `(a | b)` denotes the Jacobi/Legendre symbol.

Now, let `p` be a Legendre stack.
Let `M` be an additive monoid and `c` be a 2-torsion element of `M`.
The **Legendre stack map associated with `p` and `c`** is the map `φ` given by
  `φ(n) = c` if `(n | p_n) = -1` and `φ(n) = 0` otherwise.
We construct it as an additive map; it turns out that this map is additive.

The Legendre symbol is implemented as Jacobi symbol to avoid requiring primality instances.
-/

namespace IMOSL
namespace IMO2020N5

open zmod
open_locale number_theory_symbols



structure legendre_stack :=
(prime_chain : ℕ → ℕ)
(is_prime' : ∀ n : ℕ, (prime_chain n).prime)
(ascending' : strict_mono prime_chain)
(stacking' : ∀ n : ℕ, prime_chain n.succ ≡ prime_chain n [MOD 4 * (prime_chain n).pred.factorial])



namespace legendre_stack

instance : has_coe_to_fun legendre_stack (λ _, ℕ → ℕ) := ⟨legendre_stack.prime_chain⟩

variable (p : legendre_stack)

lemma is_prime : ∀ n : ℕ, (p n).prime := p.is_prime'
lemma ascending : strict_mono p := p.ascending'
lemma stacking : ∀ n : ℕ, p n.succ ≡ p n [MOD 4 * (p n).pred.factorial] := p.stacking'

/-- A raw bound: `n < p_n` for any `n : ℕ`. -/
lemma self_lt : ∀ n : ℕ, n < p n :=
  λ n, nat.rec_on n (p.is_prime 0).pos
    (λ n h, lt_of_le_of_lt (nat.succ_le_iff.mpr h) (p.ascending n.lt_succ_self))

/-- Equivalence of primes in the chain modulo `4`. -/
lemma eq_mod_four (k m : ℕ) : p k ≡ p m [MOD 4] :=
begin
  wlog : k ≤ m,
  refine nat.le_induction rfl (λ n _ h, h.trans _) m case,
  exact (nat.modeq.of_modeq_mul_right _ (p.stacking n)).symm
end

/-- Each prime in the chain must be odd. -/
lemma odd (n : ℕ) : odd (p n) :=
begin
  have h := p.eq_mod_four n 2,
  rw [bit0, ← two_mul] at h,
  replace h := nat.modeq.of_modeq_mul_right _ h,
  rw nat.modeq at h,
  rw [nat.odd_iff, h],
  exact (or_iff_right (ne_of_gt (p.self_lt 2))).mp (p.is_prime 2).eq_two_or_odd
end

/-- Stronger modular equivalence; for any `k ≤ m`, `p_m ≡ p_k (mod 4(p_k - 1)!). -/
lemma eq_mod_factorial {k m : ℕ} (h : k ≤ m) : p m ≡ p k [MOD 4 * (p k).pred.factorial] :=
begin
  refine nat.le_induction rfl (λ n h0 h1, nat.modeq.trans _ h1) _ h,
  obtain ⟨c, h2⟩ : (p k).pred.factorial ∣ (p n).pred.factorial :=
    nat.factorial_dvd_factorial (nat.pred_le_pred (p.ascending.monotone h0)),
  refine nat.modeq.of_modeq_mul_right c _,
  rw [mul_assoc, ← h2],
  exact p.stacking n
end



/-- For any `k : ℕ`, `(0 | p k) = 0`. -/
theorem legendre_zero_left (k : ℕ) : J(0 | p k) = 0 :=
  jacobi_sym.zero_left (p.is_prime k).one_lt

/-- For any `n : ℤ` with `n ≠ 0`, `(n | p n) = ±1`. -/
theorem legendre_ne_zero {n : ℕ} (h : n ≠ 0) : J(n | p n) = 1 ∨ J(n | p n) = -1 :=
begin
  apply jacobi_sym.eq_one_or_neg_one,
  rw [int.gcd_eq_nat_abs, int.nat_abs_of_nat, int.nat_abs_of_nat,
      ← nat.coprime_iff_gcd_eq_one, nat.coprime_comm, (p.is_prime n).coprime_iff_not_dvd],
  exact nat.not_dvd_of_pos_of_lt (zero_lt_iff.mpr h) (p.self_lt n)
end

/-- For any `b : ℤ` and `k m : ℕ` with `|b| < p_k` and `k ≤ m`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_int' {b : ℤ} {k m : ℕ} (hk : b.nat_abs < p k) (hkm : k ≤ m) :
  J(b | p k) = J(b | p m) :=
begin
  rcases eq_or_ne b 0 with rfl | hb,
  rw [legendre_zero_left, legendre_zero_left],
  rw [jacobi_sym.mod_right _ (odd p k), jacobi_sym.mod_right _ (odd p m)],
  congr' 1; rw ← nat.modeq,
  suffices : b.nat_abs ∣ (p k).pred.factorial,
  { cases this with c h,
    refine (nat.modeq.of_modeq_mul_right c _).symm,
    rw [mul_assoc, ← h]; exact eq_mod_factorial p hkm },
  refine nat.dvd_factorial (int.nat_abs_pos_of_ne_zero hb) _,
  rwa [nat.pred_eq_sub_one, ← nat.lt_iff_le_pred (p.is_prime k).pos]
end

/-- For any `b : ℤ` and `k m : ℕ` with `|b| < min{p_k, p_m}`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_int {b : ℤ} {k m : ℕ} (hk : b.nat_abs < p k) (hm : b.nat_abs < p m) :
  J(b | p k) = J(b | p m) :=
  by wlog : k ≤ m; exact legendre_equiv_int' p hk case

/-- For any `b k m : ℕ` with `b < p_k` and `k ≤ m`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_nat' {b k m : ℕ} (hk : b < p k) (hkm : k ≤ m) : J(b | p k) = J(b | p m) :=
  by convert legendre_equiv_int' p _ hkm; rwa int.nat_abs_of_nat

/-- For any `b k m : ℕ` with `b < min{p_k, p_m}`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_nat {b k m : ℕ} (hk : b < p k) (hm : b < p m) : J(b | p k) = J(b | p m) :=
  by wlog : k ≤ m; exact legendre_equiv_nat' p hk case

/-- An invariant for `p` based on congruence mod `4`, taking values `-1` or `1`. -/
def mod4_invariant := J(-1 | p 0)

/-- For any `k : ℕ`, `(-1 | p k) = mod4_invariant p`. -/
theorem legendre_equiv_mod4 (k : ℕ) : J(-1 | p k) = p.mod4_invariant :=
  eq_comm.mp (legendre_equiv_int' p (p.is_prime 0).one_lt k.zero_le)



section monoid_map

variables {M : Type*} [add_comm_monoid M] (c : M) (hc : 2 • c = 0)
include hc

/-- The Legendre stack map associated with `p` and `c` as an additive map. -/
def map : additive_map M :=
{ to_fun := λ n, ite (J(n | p n) = -1) c 0,
  map_zero' := by rw [nat.cast_zero, legendre_zero_left, if_neg (by norm_num : (0 : ℤ) ≠ -1)],
  map_one' := by rw [nat.cast_one, jacobi_sym.one_left, if_neg (by norm_num : (1 : ℤ) ≠ -1)],
  map_mul' := λ x y hx hy, begin
    have X : ∀ {a b : ℕ}, b ≠ 0 → J(a | p a) = J(a | p (a * b)) := λ a b hb,
      legendre_equiv_nat' p (p.self_lt a) (nat.le_mul_of_pos_right (zero_lt_iff.mpr hb)),
    rw [nat.cast_mul, jacobi_sym.mul_left, ← X hy, mul_comm x y, ← X hx],
    replace X : (1 : ℤ) ≠ -1 := by norm_num,
    cases legendre_ne_zero p hx with hx0 hx0; cases legendre_ne_zero p hy with hy0 hy0,
    all_goals { simp only [hx0, hy0,if_true, eq_self_iff_true, if_false, X,
      zero_add, add_zero, one_mul, mul_one, neg_mul_neg] },
    rw [← two_nsmul, ← hc]
  end }



/-- The map is zero if `c = 0`. -/
theorem map_is_zero (h : 2 • 0 = 0) : p.map 0 h = 0 :=
begin
  sorry
end

/-- The map is never zero if `c ≠ 0`. -/
theorem map_is_non_zero : p.map c hc = 0 :=
begin
  sorry
end

end monoid_map

end legendre_stack

end IMO2020N5
end IMOSL
