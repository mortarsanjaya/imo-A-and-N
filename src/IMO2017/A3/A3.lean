import data.fintype.card

/-! # IMO 2017 A3 -/

open function

namespace IMOSL
namespace IMO2017A3

variables {S : Type*} [fintype S] [decidable_eq S]

def fn_prop (f : S → S) := ∀ g : S → S, f ∘ g ∘ f = g ∘ f ∘ g → g = f



namespace extra

/-- There exists m, k ∈ ℕ such that 0 < k and f^m = f^{m + k} -/
lemma exists_iterate_eq (f : S → S) : ∃ m k : ℕ, 0 < k ∧ (f^[m + k] = (f^[m])) :=
begin
  have h := not_injective_infinite_fintype (nat.iterate f),
  simp_rw [injective, not_forall] at h,
  rcases h with ⟨m, n, h, h0⟩,
  wlog h1 : m < n := lt_or_gt_of_ne h0 using [m n, n m],
  use [m, n - m]; split,
  exact nat.sub_pos_of_lt h1,
  rw [nat.add_sub_of_le (le_of_lt h1), h]
end

lemma iterate_preperiod_add {f : S → S} {m k : ℕ} (h : 0 < k) (h0 : f^[m + k] = (f^[m])) (n : ℕ) :
  f^[m + n + k] = (f^[m + n]) :=
by rw [add_right_comm, iterate_add, h0, iterate_add]

lemma iterate_preperiod_mul {f : S → S} {m k : ℕ} (h : 0 < k) (h0 : f^[m + k] = (f^[m])) (n : ℕ) :
  f^[m + n * k] = (f^[m]) :=
begin
  induction n with n n_ih,
  rw [zero_mul, add_zero],
  rw [nat.succ_mul, ← add_assoc, iterate_add, n_ih, ← iterate_add, h0]
end

lemma exists_iterate_idempotent (f : S → S) : ∃ m : ℕ, 0 < m ∧ ((f^[m])^[2] = (f^[m])) :=
begin
  rcases exists_iterate_eq f with ⟨m, k, h, h0⟩,
  suffices : ∃ l : ℕ, m < l ∧ k ∣ l,
  { rcases this with ⟨l, h1, n, h2⟩,
    use l; split,
    exact pos_of_gt h1,
    rcases le_iff_exists_add.mp (le_of_lt h1) with ⟨c, h3⟩,
    have h4 := iterate_preperiod_mul h (iterate_preperiod_add h h0 c) n,
    rwa [← h3, mul_comm, ← h2, ← mul_two, iterate_mul] at h4 },
  use m + (k - (m % k)),
  replace h := nat.mod_lt m h,
  rw [lt_add_iff_pos_right, tsub_pos_iff_lt, and_iff_right h,
      ← nat.add_sub_assoc (le_of_lt h), add_comm, nat.add_sub_assoc (nat.mod_le _ _)],
  exact (nat.dvd_add (dvd_refl k) (nat.dvd_sub_mod m))
end

end extra



/-- Final solution -/
theorem final_solution {f : S → S} (fprop : fn_prop f) :
  f '' (set.range f) = set.range f :=
begin
  rw set.ext_iff; intros x,
  simp only [set.mem_range, set.mem_image, exists_exists_eq_and]; split,
  rintros ⟨y, h⟩; use (f y); exact h,
  rintros ⟨y, h⟩,
  rcases extra.exists_iterate_idempotent f with ⟨M, h0, h1⟩,
  use (f^[M.pred] y),
  rw [← comp_app f (f^[_]), ← comp_app f, comp_iterate_pred_of_pos f h0, ← iterate_succ'],
  subst h; revert y,
  rw ← funext_iff; simp only [],
  apply fprop,
  rw ← iterate_mul at h1,
  simp_rw [← iterate_succ, ← iterate_succ', nat.succ_eq_add_one, add_assoc],
  rw [← iterate_add, add_add_add_comm, ← mul_two M, iterate_add f M, iterate_add f (M * 2), h1]
end

end IMO2017A3
end IMOSL
