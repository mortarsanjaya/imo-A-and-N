import data.fintype.card tactic.abel

/-! # IMO 2017 A3 -/

namespace IMOSL
namespace IMO2017A3

open function set

def elt_prop {M : Type*} [monoid M] [fintype M] (x : M) := ∀ y : M, x * y * x = y * x * y → y = x



namespace extra

section monoid

variables {M : Type*} [monoid M] [fintype M]

/-- There exists m, k ∈ ℕ such that 0 < k and f^m = f^{m + k} -/
lemma exists_pow_eq (x : M) : ∃ m k : ℕ, 0 < k ∧ x ^ (m + k) = x ^ m :=
begin
  have h := not_injective_infinite_finite (λ n : ℕ, x ^ n),
  simp_rw [injective, not_forall] at h,
  rcases h with ⟨m, n, h, h0⟩,
  wlog h1 : m < n := lt_or_gt_of_ne h0 using [m n, n m],
  use [m, n - m]; split,
  exact nat.sub_pos_of_lt h1,
  rw [nat.add_sub_of_le (le_of_lt h1), h]
end

lemma pow_preperiod_add {x : M} {m k : ℕ} (h : 0 < k) (h0 : x ^ (m + k) = x ^ m) (n : ℕ) :
  x ^ (m + n + k) = x ^ (m + n) :=
by rw [add_right_comm, pow_add, h0, pow_add]

lemma pow_preperiod_mul {x : M} {m k : ℕ} (h : 0 < k) (h0 : x ^ (m + k) = x ^ m) (n : ℕ) :
  x ^ (m + n * k) = x ^ m :=
begin
  induction n with n n_ih,
  rw [zero_mul, add_zero],
  rw [nat.succ_mul, ← add_assoc, pow_add, n_ih, ← pow_add, h0]
end

lemma exists_pow_idempotent (x : M) : ∃ m : ℕ, 0 < m ∧ x ^ (2 * m) = x ^ m :=
begin
  rcases exists_pow_eq x with ⟨m, k, h, h0⟩,
  suffices : ∃ l : ℕ, m < l ∧ k ∣ l,
  { rcases this with ⟨l, h1, n, h2⟩,
    refine ⟨l, pos_of_gt h1, _⟩,
    rcases le_iff_exists_add.mp (le_of_lt h1) with ⟨c, h3⟩,
    have h4 := pow_preperiod_mul h (pow_preperiod_add h h0 c) n,
    rwa [← h3, mul_comm, ← h2, ← mul_two, mul_comm] at h4 },
  replace h := nat.mod_lt m h,
  refine ⟨m + (k - (m % k)), by rwa [lt_add_iff_pos_right, tsub_pos_iff_lt], _⟩,
  rw [← nat.add_sub_assoc (le_of_lt h), add_comm, nat.add_sub_assoc (nat.mod_le _ _)],
  exact (nat.dvd_add (dvd_refl k) (nat.dvd_sub_mod m))
end

end monoid



lemma range_sq_eq_range_of_iter_eq_self {S : Type*} (f : S → S) (h : ∃ m : ℕ, 1 < m ∧ (f^[m] = f)) :
  range (f^[2]) = range f :=
begin
  rcases h with ⟨m, h, h0⟩,
  rw set.ext_iff; intros x,
  simp only [set.mem_range]; split,
  rintros ⟨y, h⟩; use f y; exact h,
  rintros ⟨y, h⟩; use (f^[m - 2]) y,
  rw [← comp_app (f^[2]), ← iterate_add, nat.add_sub_of_le, h0, h],
  rwa nat.succ_le_iff
end

/-- Copied straight from `function.End.monoid` implementation.
  In fact, I am wondering why `function.End.monoid` cannot be used for `S → S`. -/
instance function.End.monoid' (S : Type*) : monoid (S → S) :=
{ one := id,
  mul := (∘),
  mul_assoc := λ f g h, rfl,
  mul_one := λ f, rfl,
  one_mul := λ f, rfl }

lemma pow_eq_iterate {S : Type*} (f : S → S) (m : ℕ) : f ^ m = (f^[m]) :=
begin
  induction m with m m_ih,
  rw [iterate_zero, pow_zero]; refl,
  rw [iterate_succ', pow_succ, m_ih]; refl
end

end extra



private lemma elt_prop_main_claim {M : Type*} [monoid M] [fintype M] {x : M} (h : elt_prop x) :
  ∃ m : ℕ, 1 < m ∧ x ^ m = x :=
begin
  rcases extra.exists_pow_idempotent x with ⟨m, h0, h1⟩,
  refine ⟨m + 1, nat.succ_lt_succ h0, h _ _⟩,
  rw [← pow_succ', ← pow_succ, ← pow_succ', ← pow_add],
  replace h1 := congr_arg (has_mul.mul (x ^ 3)) h1,
  rw [← pow_add, ← pow_add, eq_comm] at h1; convert h1 using 2; abel,
  rw [smul_eq_mul, smul_eq_mul, mul_one, add_comm]
end



/-- Final solution -/
theorem final_solution {S : Type*} [fintype S] [decidable_eq S] {f : S → S} (fprop : elt_prop f) :
  range (f^[2]) = range f :=
begin
  refine extra.range_sq_eq_range_of_iter_eq_self f _,
  rcases elt_prop_main_claim fprop with ⟨m, h, h0⟩,
  exact ⟨m, h, by rw [← extra.pow_eq_iterate, h0]⟩
end

end IMO2017A3
end IMOSL
