import
  data.nat.prime
  algebra.group.defs
  algebra.module.basic
  data.set.finite
  data.nat.log
  data.nat.gcd
  data.nat.modeq
  field_theory.finite.basic

/-! # IMO 2020 N5, Generalized Version -/

open function set
open_locale classical

namespace IMOSL
namespace IMO2020N5



section extra_lemmas

private lemma nat.not_div_iff_mod_pos {a b : ℕ} : ¬a ∣ b ↔ 0 < b % a :=
  by rw [zero_lt_iff, ne.def, ← nat.dvd_iff_mod_eq_zero]

end extra_lemmas







/-! # Definitions -/
section defs

variables {M : Type*} [add_comm_monoid M]

def additive (f : ℕ → M) := ∀ x y : ℕ, 0 < x → 0 < y → f (x * y) = f x + f y
def good (n : ℕ) (f : ℕ → M) := ∀ a b : ℕ, 0 < a → 0 < b → a + b = n → f a = f b
def wide (f : ℕ → M) := {p : ℕ | p.prime ∧ good p f}.infinite
def strong {p : ℕ} (hp : p.prime) (f : ℕ → M) := ∀ k : ℕ, good (p ^ k) f

end defs



/-! # General results -/
section general

variables {M : Type*} [add_cancel_comm_monoid M]

private lemma trivial_lem1 (f : ℕ → M) : good 1 f :=
begin
  rintros a b ha hb h,
  exfalso; refine ne_of_gt _ h,
  rw ← nat.succ_le_iff at ha hb ⊢,
  exact add_le_add ha hb
end

private lemma trivial_lem2 {f : ℕ → M} (fadd : additive f)
  {d n : ℕ} (h : 0 < n) (h0 : d ∣ n) (h1 : good n f) : good d f :=
begin
  rcases h0 with ⟨c, rfl⟩,
  rcases c.eq_zero_or_pos with rfl | hc,
  exfalso; rw mul_zero at h; exact lt_irrefl 0 h,
  intros a b ha hb h0,
  replace h1 := h1 (a * c) (b * c) (mul_pos ha hc) (mul_pos hb hc) (by rw [← add_mul, h0]),
  rwa [fadd a c ha hc, fadd b c hb hc, add_left_inj] at h1
end

private lemma trivial_lem3 {f : ℕ → M} (fadd : additive f) : f 1 = 0 :=
begin
  replace fadd := fadd 1 1 one_pos one_pos,
  rwa [mul_one, self_eq_add_left] at fadd
end



private lemma general_lem1_1 {f : ℕ → M} (fadd : additive f)
  {p : ℕ} (hp : p.prime) (h : ¬strong hp f) : ∃ c : ℕ, ∀ k : ℕ, good (p ^ k) f ↔ k ≤ c :=
begin
  simp only [strong, not_exists, not_forall] at h,
  set c := nat.find h with hc,
  have h1 : ¬good (p ^ c) f := nat.find_spec h,
  clear_value c; cases c with c c,
  rw pow_zero at h1,
  exfalso; exact h1 (trivial_lem1 f),
  refine ⟨c, λ k, ⟨λ h0, _, λ h0, _⟩⟩,
  { rw [← not_lt, ← nat.succ_le_iff]; intros h2,
    exact h1 (trivial_lem2 fadd (pow_pos hp.pos _) (pow_dvd_pow p h2) h0) },
  { refine not_not.mp (nat.find_min h _),
    rwa [← hc, nat.lt_succ_iff] }
end

private lemma general_lem1_2 {f : ℕ → M} (fadd : additive f) (h : ¬wide f) :
  {p : nat.primes | good p f}.finite :=
begin
  contrapose h,
  simp only [wide, not_not],
  suffices : coe '' {p : nat.primes | good p f} = {p : ℕ | p.prime ∧ good p f},
  { rwa [← this, infinite_image_iff],
    exact inj_on_of_injective subtype.coe_injective _ },
  ext p; simp only [set.mem_image, set.mem_set_of_eq]; split,
  rintros ⟨⟨p, hp⟩, h0, rfl⟩; exact ⟨hp, h0⟩,
  rintros ⟨hp, h0⟩; exact ⟨⟨p, hp⟩, h0, rfl⟩
end

private theorem general1 {f : ℕ → M} (fadd : additive f) :
  {n : ℕ | good n f}.infinite ↔ wide f ∨ ∃ {p : ℕ} (hp : p.prime), strong hp f :=
begin
  symmetry; split,
  { rintros (h | ⟨p, hp, h⟩),
    refine infinite.mono (λ x hx, _) h; exact hx.right,
    refine infinite.mono _ (infinite_range_of_injective (nat.pow_right_injective hp.two_le)),
    rintros x ⟨c, h0⟩,
    rw ← h0; exact h c },
  { intros h; contrapose! h,
    rw not_infinite,
    suffices : ∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, good n f ↔ n = 0 ∨ n ∣ N,
    { rcases this with ⟨N, hN, this⟩,
      refine finite.subset (finset.range N.succ).finite_to_set (λ n h0, _),
      rw [finset.mem_coe, finset.mem_range, nat.lt_succ_iff],
      rw [set.mem_set_of_eq, this] at h0,
      rcases h0 with rfl | h0,
      exacts [N.zero_le, nat.le_of_dvd hN h0] },

    /- First show, using AOC, that there is a sequence (x_p) with the desired property. -/
    replace h : ∃ x : nat.primes →₀ ℕ, ∀ {p : ℕ} (hp : p.prime) (k : ℕ),
      good (p ^ k) f ↔ k ≤ x ⟨p, hp⟩ :=
    begin
      cases h with h h0,
      replace h := general_lem1_2 fadd h,
      replace h0 : ∃ x : nat.primes → ℕ, ∀ (p : nat.primes) (k : ℕ), good (p ^ k) f ↔ k ≤ x p :=
      begin
        suffices : ∀ p : nat.primes, ∃ kp : ℕ, (∀ k : ℕ, good (p ^ k) f ↔ k ≤ kp),
          exact classical.axiom_of_choice this,
        rintros ⟨p, hp⟩,
        rw subtype.coe_mk,
        exact general_lem1_1 fadd hp (h0 hp)
      end,
      rcases h0 with ⟨x, h0⟩,
      refine ⟨⟨h.to_finset, x, (λ p, _)⟩, (λ p hp, h0 ⟨p, hp⟩)⟩,
      rw [set.finite.mem_to_finset, set.mem_set_of_eq,
          ← pos_iff_ne_zero, ← nat.succ_le_iff, ← h0, pow_one]
    end,

    /- Now show that there exists N < ∞ such that for any n, good n f ↔ n = 0 ∨ n | N -/
    sorry },

end

private lemma general2 {f : ℕ → M} (fadd : additive f) {p : ℕ} (hp : p.prime) (h : good p f)
  {k m : ℕ} (hkp : ¬p ∣ k) (hmp : ¬p ∣ m) : f ((k * m) % p) = f (k % p) + f (m % p) :=
begin
  sorry
end

private lemma general3 {f : ℕ → M} (fadd : additive f) {p : ℕ} (hp : p.prime) (h : good p f)
  {k : ℕ} (hkp : ¬p ∣ k) (t : ℕ) : f ((k ^ t) % p) = t • f (k % p) :=
begin
  induction t with t t_ih,
  rw [zero_smul, pow_zero, nat.mod_eq_of_lt hp.one_lt, trivial_lem3 fadd],
  rw [nat.succ_eq_add_one, pow_succ', add_smul, one_smul, general2 fadd hp h _ hkp, t_ih],
  rw ← nat.prime.coprime_iff_not_dvd hp at hkp ⊢,
  exact nat.coprime.pow_right t hkp
end

private lemma general4 [no_zero_smul_divisors ℕ M] {f : ℕ → M} (fadd : additive f)
  {p : ℕ} (hp : p.prime) (h : good p f) {k : ℕ} (hk : 0 < k) (hkp : k < p) : f k = 0 :=
begin
  have h0 := nat.not_dvd_of_pos_of_lt hk hkp,
  have h1 : k ^ (p - 1) % p = 1 :=
  begin
    rw [← nat.prime.coprime_iff_not_dvd hp, nat.coprime_comm] at h0,
    replace h0 := nat.modeq.pow_totient h0,
    rwa [nat.modeq, nat.totient_prime hp, nat.mod_eq_of_lt hp.one_lt] at h0
  end,
  replace h := general3 fadd hp h h0 (p - 1),
  rwa [h1, trivial_lem3 fadd, eq_comm, smul_eq_zero, nat.sub_eq_zero_iff_le,
       or_iff_right (not_le_of_lt hp.one_lt), nat.mod_eq_of_lt hkp] at h
end

end general







end IMO2020N5
end IMOSL
