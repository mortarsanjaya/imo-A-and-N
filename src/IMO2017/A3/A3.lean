import
  data.fintype.basic
  data.fintype.card
  logic.function.basic
  tactic.norm_num

namespace IMO2017A3

variable {S : Type}
variable [fintype S]
variable [decidable_eq S]

/--
  IMO 2017 A3

  Let S be a finite set, and fix some f : S → S.
  Suppose that, for any g : S → S, f ∘ g ∘ f = g ∘ f ∘ g implies g = f.
  Prove that f(f(S)) = f(S).

  See http://www.imo-official.org/problems/IMO2017SL.pdf
  We will partially follow the official solution.
  It suffices to prove that there exists a positive integer n such that
          f^{n + 3} = f^{2n + 3}
  Then we proceed as in the claim: use this property to show that f(f(S)) = f(S).
-/
def fn_prop (f : S → S) := ∀ g : S → S, f ∘ g ∘ f = g ∘ f ∘ g → g = f



open function







namespace solution

variable {f : S → S}
variable fprop : fn_prop f
include fprop



lemma fn_lem1 : ∃ m n : ℕ, m < n ∧ nat.iterate f m = nat.iterate f n :=
begin
  have h := not_injective_infinite_fintype (nat.iterate f),
  unfold injective at h,
  simp_rw not_forall at h,
  rcases h with ⟨m, n, h, h0⟩,
  change ¬m = n with m ≠ n at h0,
  rw ne_iff_lt_or_gt at h0,
  cases h0,
  use [m, n]; split; assumption,
  use [n, m]; split,
  exact h0,
  rw h,
end

lemma fn_lem2 : ∃ m : ℕ, 0 < m ∧ nat.iterate f (2 * m) = nat.iterate f m :=
begin
  rcases fn_lem1 fprop with ⟨m, n, h, h0⟩,
  let k := n - m,
  let l := n + (k - (n % k)),
  use l; split,
  exact nat.lt_add_right 0 n _ (pos_of_gt h),

  rw [← nat.add_sub_cancel_left m n, nat.add_sub_assoc (le_of_lt h)] at h0,
  have h1 : ∀ c : ℕ, m ≤ c → nat.iterate f (c + k) = nat.iterate f c,
  { intros c h1,
    rw le_iff_exists_add' at h1,
    cases h1 with d h1,
    rw [h1, add_assoc, iterate_add, ← h0, iterate_add] },

  have h2 : k ∣ l,
  { change l with n + (k - n % k),
    rw [← nat.add_sub_assoc, add_comm, nat.add_sub_assoc (nat.mod_le _ _)],
    exact (nat.dvd_add (dvd_refl k) (nat.dvd_sub_mod n)),
    refine le_of_lt (nat.mod_lt n _),
    rwa tsub_pos_iff_lt },
  
  ---- Take a such that l = ak, then induction on a
  cases h2 with a h2,
  rw two_mul; nth_rewrite 1 h2; clear h2,
  induction a with a a_ih,
  rw [mul_zero, add_zero],
  rw [nat.succ_eq_add_one, mul_add, mul_one, ← add_assoc,
      iterate_add, a_ih, ← iterate_add, h1],
  refine le_of_lt (lt_of_lt_of_le h _),
  exact le_self_add,
end

lemma fn_lem3 : ∃ N : ℕ, 0 < N ∧ nat.iterate f (N + 1) = f :=
begin
  rcases fn_lem2 fprop with ⟨m, h, h0⟩,
  use m; split,
  exact h,
  apply fprop,
  rw [← iterate_succ, ← iterate_succ', ← iterate_succ', ← iterate_add,
      nat.succ_eq_add_one, nat.succ_eq_add_one, add_assoc, add_assoc,
      add_assoc m 1 1, add_add_add_comm, ← two_mul m, iterate_add,
      ← h0, ← iterate_add],
end

theorem IMO2017A3_sol : f '' (set.range f) = set.range f :=
begin
  rw set.ext_iff; intros x,
  rw [set.mem_image, set.mem_range]; split,

  { intros h,
    rcases h with ⟨y, h, h0⟩,
    use y; exact h0 },
  
  { intros h,
    cases h with y h,
    rcases fn_lem3 fprop with ⟨N, h0, h1⟩,
    use nat.iterate f N y; split,
    rw set.mem_range; use nat.iterate f (N - 1) y,
    rw [← comp_apply f, ← iterate_succ', nat.succ_eq_add_one, nat.sub_add_cancel],
    rw ← nat.lt_iff_add_one_le; exact h0,
    rw [← comp_apply f, ← iterate_succ', nat.succ_eq_add_one, h1, h] },
end



end solution







end IMO2017A3
