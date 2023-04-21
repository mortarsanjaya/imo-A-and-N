import
  IMO2020.N5.additive_map
  number_theory.legendre_symbol.jacobi_symbol
  extra.number_theory.dirichlet_thm_arithmetic_progression

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
  wlog h : k ≤ m,
  refine (this p m k $ le_of_not_ge h).symm,
  refine nat.le_induction rfl (λ n _ h, h.trans _) m h,
  exact (nat.modeq.of_mul_right _ $ p.stacking n).symm
end

/-- Each prime in the chain must be odd. -/
lemma odd (n : ℕ) : odd (p n) :=
begin
  have h := p.eq_mod_four n 2,
  rw [bit0, ← two_mul] at h,
  replace h := nat.modeq.of_mul_right _ h,
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
  refine nat.modeq.of_mul_right c _,
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
    refine (nat.modeq.of_mul_right c _).symm,
    rw [mul_assoc, ← h]; exact eq_mod_factorial p hkm },
  refine nat.dvd_factorial (int.nat_abs_pos_of_ne_zero hb) _,
  rwa [nat.pred_eq_sub_one, ← nat.lt_iff_le_pred (p.is_prime k).pos]
end

/-- For any `b : ℤ` and `k m : ℕ` with `|b| < min{p_k, p_m}`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_int {b : ℤ} {k m : ℕ} (hk : b.nat_abs < p k) (hm : b.nat_abs < p m) :
  J(b | p k) = J(b | p m) :=
begin
  wlog h : k ≤ m,
  refine (this p hm hk $ le_of_not_le h).symm,
  exact legendre_equiv_int' p hk h,
end

/-- For any `b k m : ℕ` with `b < p_k` and `k ≤ m`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_nat' {b k m : ℕ} (hk : b < p k) (hkm : k ≤ m) : J(b | p k) = J(b | p m) :=
  by convert legendre_equiv_int' p _ hkm; rwa int.nat_abs_of_nat

/-- For any `b k m : ℕ` with `b < min{p_k, p_m}`, we have `(b | p_k) = (b | p_m)`. -/
theorem legendre_equiv_nat {b k m : ℕ} (hk : b < p k) (hm : b < p m) : J(b | p k) = J(b | p m) :=
begin
  wlog h : k ≤ m,
  refine (this p hm hk $ le_of_not_le h).symm,
  exact legendre_equiv_nat' p hk h
end

/-- An invariant for `p` based on congruence mod `4`, taking values `-1` or `1`. -/
def χ₄ := χ₄ (p 0)

/-- For any `k : ℕ`, `(-1 | p k) = χ₄ p`. -/
theorem legendre_equiv_χ₄ (k : ℕ) : J(-1 | p k) = p.χ₄ :=
begin
  rw [← legendre_equiv_int' p _ k.zero_le, jacobi_sym.at_neg_one (p.odd 0), χ₄],
  rw [int.nat_abs_neg, int.nat_abs_one]; exact (p.is_prime 0).one_lt
end

/-- `χ₄ p = ± 1`. -/
theorem χ₄_eq_one_or_neg_one : p.χ₄ = 1 ∨ p.χ₄ = -1 :=
begin
  rw ← p.legendre_equiv_χ₄ 0,
  apply jacobi_sym.eq_one_or_neg_one,
  rw [int.gcd_eq_nat_abs, int.nat_abs_of_nat, int.nat_abs_neg, int.nat_abs_one, nat.gcd_one_left]
end

/-- For any `b : ℤ` and `k : ℕ`, `(-b | p k) = χ₄ p * (b | p k)` -/
theorem legendre_neg (b : ℤ) (k : ℕ) : J(-b | p k) = χ₄ p * J(b | p k) :=
  by rw [← legendre_equiv_χ₄ p k, ← jacobi_sym.mul_left, neg_one_mul]



section monoid_map

/-- The Legendre stack map associated with `p` and `c` as an additive map. -/
def map {M : Type*} [add_monoid M] (c : M) (hc : 2 • c = 0) : additive_map M :=
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


variables {M : Type*} [add_comm_monoid M] {c : M} (hc : 2 • c = 0)
include hc

theorem map_val (n : ℕ) : p.map c hc n = ite (J(n | p n) = -1) c 0 := rfl

theorem map_val' {n k : ℕ} (h : n < p k) : p.map c hc n = ite (J(n | p k) = -1) c 0 :=
  by rw [map_val, p.legendre_equiv_nat (p.self_lt n) h]

/-- The map is never zero if `c ≠ 0`. -/
theorem map_is_non_zero (h : c ≠ 0) : p.map c hc ≠ 0 :=
begin
  haveI : fact (p 0).prime := ⟨p.is_prime 0⟩,
  obtain ⟨a, ha, h0⟩ : ∃ a : ℕ, a < p 0 ∧ ¬is_square ((a : ℤ) : zmod (p 0)) :=
  begin
    suffices : ∃ a : zmod (p 0), ¬is_square a,
    { cases this with a h0,
      refine ⟨a.val, val_lt a, _⟩,
      rwa [zmod.nat_cast_val, zmod.int_cast_cast, zmod.cast_id', id.def] },
    refine finite_field.exists_nonsquare (λ h0, _),
    rw zmod.ring_char_zmod_n at h0,
    have h1 := p.odd 0,
    rw [h0, nat.odd_iff_not_even] at h1,
    exact h1 even_two
  end,
  rw [← zmod.nonsquare_iff_jacobi_sym_eq_neg_one, legendre_equiv_nat' p ha a.zero_le] at h0,
  intros h1; replace h1 := fun_like.congr_fun h1 a,
  rw [additive_map.zero_apply, p.map_val, if_pos h0] at h1,
  exact h h1
end

/-- The map is zero iff `c = 0`. -/
theorem map_is_zero_iff : p.map c hc = 0 ↔ c = 0 :=
begin
  split; intros h,
  by_contra h0; exact p.map_is_non_zero hc h0 h,
  ext n; rw [additive_map.zero_apply, map_val, h, if_t_t]
end

theorem map_mul_mod {a b m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (ha0 : a < p m) (hb0 : b < p m) :
  p.map c hc a + p.map c hc b = p.map c hc (a * b % p m) :=
begin
  rw [p.map_val, p.map_val, p.map_val' hc (nat.mod_lt _ (p.is_prime m).pos),
      int.coe_nat_mod, ← jacobi_sym.mod_left, nat.cast_mul, jacobi_sym.mul_left,
      p.legendre_equiv_nat ha0 (p.self_lt a), p.legendre_equiv_nat hb0 (p.self_lt b)],
  have X : (1 : ℤ) ≠ -1 := by norm_num,
  cases legendre_ne_zero p ha with ha1 ha1; cases legendre_ne_zero p hb with hb1 hb1,
  all_goals { simp only [ha1, hb1, if_true, eq_self_iff_true, if_false, X,
    zero_add, add_zero, one_mul, mul_one, neg_mul_neg] },
  rw [← two_nsmul, ← hc]
end

theorem map_p_sub {n k : ℕ} (h : n ≠ 0) (h0 : n < p k) :
  p.map c hc (p k - n) = ite (p.χ₄ = -1) c 0 + p.map c hc n :=
begin
  have h1 : 0 < n := by rwa zero_lt_iff,
  rw [p.map_val' hc (nat.sub_lt (lt_trans h1 h0) h1), nat.cast_sub (le_of_lt h0),
      sub_eq_add_neg, jacobi_sym.mod_left, int.add_mod_self_left, ← jacobi_sym.mod_left,
      ← neg_one_mul, jacobi_sym.mul_left, p.legendre_equiv_χ₄ k, p.map_val' hc h0,
      p.legendre_equiv_nat h0 (p.self_lt n)],
  have X : (1 : ℤ) ≠ -1 := by norm_num,
  cases legendre_ne_zero p h with h2 h2; cases p.χ₄_eq_one_or_neg_one with h3 h3,
  all_goals { simp only [h2, h3, if_true, eq_self_iff_true, if_false, X,
    zero_add, add_zero, one_mul, mul_one, neg_mul_neg] },
  rw [← two_nsmul, ← hc]
end

theorem map_p_sub_χ₄_eq_one (h : p.χ₄ = 1) {n k : ℕ} (h0 : n ≠ 0) (h1 : n < p k) :
  p.map c hc (p k - n) = p.map c hc n :=
  by rw [p.map_p_sub hc h0 h1, h, if_neg (by norm_num : (1 : ℤ) ≠ -1), zero_add]

theorem map_p_sub_χ₄_eq_neg_one (h : p.χ₄ = -1) {n k : ℕ} (h0 : n ≠ 0) (h1 : n < p k)  :
  p.map c hc (p k - n) = c + p.map c hc n :=
  by rw [p.map_p_sub hc h0 h1, h, if_pos rfl]

end monoid_map

end legendre_stack





section construction

private lemma lt_four_times_pred_factorial (p : ℕ) : p < 4 * p.pred.factorial :=
begin
  cases p with p p_ih,
  rw [nat.pred_zero, nat.factorial_zero, mul_one]; norm_num,
  rw nat.pred_succ; induction p with p h,
  rw [nat.factorial_zero, mul_one]; norm_num,
  rcases p.eq_zero_or_pos with rfl | h0,
  rw [nat.factorial_one, mul_one]; norm_num,
  rw [nat.factorial_succ, mul_comm (p + 1), ← mul_assoc],
  rw ← nat.succ_le_iff at h; refine lt_of_lt_of_le _ (nat.mul_le_mul_right _ h),
  rwa [lt_mul_iff_one_lt_right p.succ.succ_pos, lt_add_iff_pos_left]
end

private lemma coprime_four_times_pred_factorial {p : ℕ} (hp : p.prime) (h : 2 < p) :
  p.coprime (4 * p.pred.factorial) :=
begin
  rw [nat.coprime_mul_iff_right, bit0, ← two_mul, ← sq]; split,
  exact nat.coprime.pow_right _ ((nat.coprime_primes hp nat.prime_two).mpr (ne_of_gt h)),
  replace h := nat.pred_lt (ne_of_gt (pos_of_gt h)),
  generalize_hyp : p.pred = k at h ⊢,
  induction k with k k_ih,
  rw nat.factorial_zero; exact p.coprime_one_right,
  rw [nat.factorial_succ, nat.coprime_mul_iff_right, and_comm]; split,
  exact k_ih (nat.lt_of_succ_lt h),
  rw hp.coprime_iff_not_dvd; exact nat.not_dvd_of_pos_of_lt k.succ_pos h
end

private lemma exists_next_stack {p : ℕ} (hp : p.prime) (h : 2 < p) :
  ∃ q : ℕ, p < q ∧ q.prime ∧ q ≡ p [MOD 4 * p.pred.factorial] :=
begin
  have X := lt_four_times_pred_factorial p,
  obtain ⟨q, h0, h1, h2⟩ :=
    extra.exists_infinite_primes_mod_eq X (coprime_four_times_pred_factorial hp h) p,
  refine ⟨q, h0, h1, _⟩,
  rw [nat.modeq, nat.mod_eq_of_lt X, h2]
end

private def next_stack_term {p : ℕ} (hp : p.prime) (h : 2 < p) :=
  nat.find (exists_next_stack hp h)

private lemma next_stack_term_prime {p : ℕ} (hp : p.prime) (h : 2 < p) :
  nat.prime (next_stack_term hp h) :=
  (nat.find_spec (exists_next_stack hp h)).2.1

private lemma next_stack_term_self_lt {p : ℕ} (hp : p.prime) (h : 2 < p) :
  p < next_stack_term hp h :=
  (nat.find_spec (exists_next_stack hp h)).1

private lemma next_stack_term_two_lt {p : ℕ} (hp : p.prime) (h : 2 < p) :
  2 < next_stack_term hp h :=
  lt_trans h (next_stack_term_self_lt hp h)

private lemma next_stack_term_mod_pred_factorial {p : ℕ} (hp : p.prime) (h : 2 < p) :
  next_stack_term hp h ≡ p [MOD 4 * p.pred.factorial] :=
  (nat.find_spec (exists_next_stack hp h)).2.2

private def bundled_next_stack_term (p' : {p : ℕ | p.prime ∧ 2 < p}) : {p : ℕ | p.prime ∧ 2 < p} :=
  ⟨next_stack_term p'.2.1 p'.2.2, next_stack_term_prime p'.2.1 p'.2.2,
   next_stack_term_two_lt p'.2.1 p'.2.2⟩

private def bundled_stack_map (p' : {p : ℕ | p.prime ∧ 2 < p}) : legendre_stack :=
{ prime_chain := λ n, (bundled_next_stack_term^[n] p').1,
  is_prime' := λ n, (bundled_next_stack_term^[n] p').2.1,
  ascending' := strict_mono_nat_of_lt_succ (λ n, by
    rw [function.iterate_succ', function.comp_app]; exact next_stack_term_self_lt _ _),
  stacking' := λ n, by rw [function.iterate_succ', function.comp_app];
    exact next_stack_term_mod_pred_factorial _ _ }

/-- Concrete legendre stack map, starting at given odd prime. -/
def concrete_stack_map {p : ℕ} (hp : p.prime) (h : 2 < p) : legendre_stack :=
  bundled_stack_map ⟨p, hp, h⟩

/-- The `χ₄` value of a concrete legendre stack map. -/
theorem concrete_stack_χ₄ {p : ℕ} (hp : p.prime) (h : 2 < p) :
  (concrete_stack_map hp h).χ₄ = χ₄ p := rfl

/-- The "standard" legendre stack map starting with `p = 5`. -/
def standard_stack_map :=
  concrete_stack_map (by norm_num : nat.prime 5) (by norm_num : 2 < 5)

/-- The `χ₄` value of the standard legendre stack map is `1`. -/
theorem standard_stack_χ₄ : standard_stack_map.χ₄ = 1 := rfl

/-- An abstraction of the existence of the standard stack. -/
theorem exists_legendre_stack_χ₄_eq_one : ∃ p : legendre_stack, p.χ₄ = 1 :=
  ⟨standard_stack_map, standard_stack_χ₄⟩

end construction

end IMO2020N5
end IMOSL
