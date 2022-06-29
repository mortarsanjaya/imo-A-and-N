import data.fintype.card

namespace IMOSL
namespace IMO2017A3

open function

variables {S : Type*} [fintype S] [decidable_eq S]

/--
  IMO 2017 A3

  Let S be a finite set, and fix some f : S → S.
  Suppose that, for any g : S → S, f ∘ g ∘ f = g ∘ f ∘ g implies g = f.
  Prove that f(f(S)) = f(S).

  See http://www.imo-official.org/problems/IMO2017SL.pdf
  We will partially follow the official solution.
  We use f^{n + 3} = f^{2n + 3} for the claim instead of f^{n + 2} = f^{2n + 1}.
  Then we proceed as in the claim: use this property to show that f(f(S)) = f(S).
-/
def fn_prop (f : S → S) := ∀ g : S → S, f ∘ g ∘ f = g ∘ f ∘ g → g = f



namespace extra

/-- There exists m, k ∈ ℕ such that 0 < k and f^m = f^{m + k} -/
lemma exists_iterate_eq (f : S → S) : ∃ m k : ℕ, 0 < k ∧ (f^[m + k] = (f^[m])) :=
begin
  have h := not_injective_infinite_fintype (nat.iterate f),
  unfold injective at h,
  simp_rw not_forall at h,
  rcases h with ⟨m, n, h, h0⟩,
  change ¬m = n with m ≠ n at h0,
  rw ne_iff_lt_or_gt at h0; cases h0,
  use [m, n - m]; split,
  exact nat.sub_pos_of_lt h0,
  rw [nat.add_sub_of_le (le_of_lt h0), h],
  use [n, m - n]; split,
  exact nat.sub_pos_of_lt h0,
  rw [nat.add_sub_of_le (le_of_lt h0), h]
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
  have h1 := nat.mod_lt m h,
  split,
  rwa [lt_add_iff_pos_right, tsub_pos_iff_lt],
  rw [← nat.add_sub_assoc (le_of_lt h1), add_comm, nat.add_sub_assoc (nat.mod_le _ _)],
  exact (nat.dvd_add (dvd_refl k) (nat.dvd_sub_mod m))
end

end extra



/-- Final solution -/
theorem final_solution {f : S → S} (fprop : fn_prop f) :
  f '' (set.range f) = set.range f :=
begin
  rw set.ext_iff; intros x,
  simp; split,
  rintros ⟨y, h⟩; use (f y); exact h,
  rintros ⟨y, h⟩,
  rcases extra.exists_iterate_idempotent f with ⟨M, h0, h1⟩,
  have h2 : (f^[M.succ]) = f :=
  begin
    apply fprop,
    rw ← iterate_mul at h1,
    simp_rw [← iterate_succ, ← iterate_succ', nat.succ_eq_add_one, add_assoc],
    rw [← iterate_add, add_add_add_comm, ← mul_two M, iterate_add f M, iterate_add f (M * 2), h1]
  end,
  use (f^[M.pred] y),
  rw [← comp_app f (f^[_]), ← comp_app f, comp_iterate_pred_of_pos f h0, ← iterate_succ', h2, h]
end

end IMO2017A3
end IMOSL
