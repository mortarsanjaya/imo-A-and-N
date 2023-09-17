import dynamics.periodic_pts ring_theory.int.basic extra.seq_max 

/-! # IMO 2020 A6 -/

namespace IMOSL
namespace IMO2020A6

open function

def good (f : ℤ → ℤ) :=
  ∀ a b : ℤ, f^[a.nat_abs ^ 2 + b.nat_abs ^ 2] (a + b) = a * f a + b * f b





/- ### Answer -/

lemma add_one_iterate : ∀ (n : ℕ) (a : ℤ), (λ x : ℤ, x + 1)^[n] a = a + n
| 0 a := a.add_zero.symm
| (n+1) a := (iterate_succ_apply' _ _ _).trans $
    (congr_arg2 _ (add_one_iterate n a) rfl).trans (a.add_assoc n 1)

lemma good_add_one : good (λ x : ℤ, x + 1) :=
  λ a b, (add_one_iterate _ _).trans $ by rw [int.coe_nat_add, int.coe_nat_pow,
    int.nat_abs_sq, int.coe_nat_pow, int.nat_abs_sq, add_add_add_comm, sq,
    ← mul_one_add, add_comm 1 a, sq, ← mul_one_add, add_comm 1 b]

lemma map_const_iterate : ∀ (n : ℕ) (a b : ℤ), (λ x : ℤ, b)^[n] a = ite (n = 0) a b
| 0 a b := (if_pos (rfl : 0 = 0)).symm
| (n+1) a b := (iterate_succ_apply' _ _ _).trans (if_neg n.succ_ne_zero).symm

lemma nat_abs_sq_eq_zero_imp {k : ℤ} (h : k.nat_abs ^ 2 = 0) : k = 0 :=
  int.nat_abs_eq_zero.mp (pow_eq_zero h)

lemma good_zero : good (λ _, 0) :=
λ a b, suffices a.nat_abs ^ 2 + b.nat_abs ^ 2 = 0 → a + b = 0 + 0,
  from (map_const_iterate _ _ _).trans $ (ite_eq_right_iff.mpr this).trans $
    (congr_arg2 _ a.mul_zero b.mul_zero).symm,
λ h, let h0 := add_eq_zero_iff.mp h in
  congr_arg2 _ (nat_abs_sq_eq_zero_imp h0.1) (nat_abs_sq_eq_zero_imp h0.2)





/- ### Solution -/

section solution

variables {f : ℤ → ℤ}

variables (h : good f)
include h

lemma map_iterate_sq (a : ℤ) : f^[a.nat_abs ^ 2] a = a * f a :=
  (congr_arg (f^[a.nat_abs ^ 2]) a.add_zero).symm.trans $
    (h a 0).trans $ add_right_eq_self.mpr (f 0).zero_mul

lemma map_neg_one : f (-1) = 0 :=
  eq_zero_of_neg_eq $ (neg_eq_neg_one_mul _).trans (map_iterate_sq h (-1)).symm

lemma map_iterate_sq_add_one (a : ℤ) : f^[a.nat_abs ^ 2 + 1] (a - 1) = a * f a :=
  (congr_arg _ int.sub_eq_add_neg).trans $ (h a (-1)).trans $
    add_right_eq_self.mpr $ mul_eq_zero_of_right _ (map_neg_one h)

lemma map_iterate_sq_add_one' (a : ℤ) :
  f^[a.nat_abs ^ 2 + 1] (a - 1) = (f^[a.nat_abs ^ 2]) a :=
  (map_iterate_sq_add_one h a).trans (map_iterate_sq h a).symm

lemma map_iterate_sq_add_one'' (a : ℤ) :
  f^[(a + 1).nat_abs ^ 2 + 1] a = (f^[(a + 1).nat_abs ^ 2]) (a + 1) :=
    (congr_arg (f^[_]) (add_sub_cancel a 1).symm).trans $ map_iterate_sq_add_one' h (a + 1)

lemma eq_add_one_of_injective (h0 : injective f) : f = (+ 1) :=
  funext $ λ a, h0.iterate ((a + 1).nat_abs ^ 2) $
    (iterate_succ_apply _ _ _).symm.trans $ map_iterate_sq_add_one'' h a



lemma exists_map_iterate_add_eq : ∀ (k : ℕ) (a : ℤ), ∃ N, (f^[N + k]) a = (f^[N]) (a + k)
| 0 a := ⟨0, a.add_zero.symm⟩
| (k+1) a := exists.elim (exists_map_iterate_add_eq k (a + 1)) $ λ N h0,
    ⟨N + (a + 1).nat_abs ^ 2, by rw [add_add_add_comm, iterate_add_apply,
      map_iterate_sq_add_one'' h, commute.iterate_iterate_self, h0,
      ← iterate_add_apply, add_comm, add_right_comm, add_assoc, ← int.coe_nat_succ]⟩

lemma exists_iterate_eq_iterate_zero (a : ℤ) : ∃ M N, (f^[M]) a = (f^[N]) 0 :=
  (le_total 0 a).elim
    (λ h0, exists.elim (exists_map_iterate_add_eq h a.nat_abs 0) $ λ N h1, ⟨N, N + a.nat_abs,
      (h1.trans $ congr_arg _ $ (a.nat_abs : ℤ).zero_add.trans $ int.nat_abs_of_nonneg h0).symm⟩)
    (λ h0, exists.elim (exists_map_iterate_add_eq h a.nat_abs a) $ λ N h1, ⟨N + a.nat_abs, N,
      h1.trans $ congr_arg _ $ add_eq_zero_iff_neg_eq.mpr (int.of_nat_nat_abs_of_nonpos h0).symm⟩)

/-- This lemma is general and independent of `f` being `good` -/
lemma exists_map_eq_map_add_pos_of_not_inj (h : ¬injective f) :
  ∃ (a : ℤ) (k : ℕ), 0 < k ∧ f a = f (a + k) :=
have ∀ a b : ℤ, f a = f b → a < b → ∃ (a : ℤ) (k : ℕ), 0 < k ∧ f a = f (a + k),
from λ a b h h0, let h1 := sub_pos_of_lt h0 in
  ⟨a, (b - a).nat_abs, int.nat_abs_pos_of_ne_zero h1.ne.symm,
    h.trans $ congr_arg f $ eq_add_of_sub_eq' $ (int.of_nat_nat_abs_eq_of_nonneg h1.le).symm⟩,
exists.elim (not_forall.mp h) $ λ a h, exists.elim (not_forall.mp h) $ λ b h,
  let h := not_imp.mp h in (lt_or_gt_of_ne h.2).elim (this a b h.1) (this b a h.1.symm)

lemma minimal_period_zero_pos_of_not_injective (h0 : ¬injective f) :
  ∃ N : ℕ, 0 < f.minimal_period (f^[N] 0) :=
begin
  rcases exists_map_eq_map_add_pos_of_not_inj h0 with ⟨a, k, h1, h2⟩,
  cases exists_map_iterate_add_eq h k a with K h3,
  replace h3 := congr_arg f h3,
  rw [← f.iterate_succ_apply', commute.self_iterate f,
      ← h2, ← f.iterate_succ_apply, ← nat.succ_add] at h3,
  rcases exists_iterate_eq_iterate_zero h a with ⟨M, N, h4⟩,
  refine ⟨K.succ + N, is_periodic_pt.minimal_period_pos h1 _⟩,
  rw [is_periodic_pt, is_fixed_pt, f.iterate_add_apply, ← h4, ← f.iterate_add_apply,
      add_comm, ← commute.iterate_iterate_self, h3, commute.iterate_iterate_self]
end

lemma orbit_zero_bounded_of_not_injective (h0 : ¬injective f) :
  ∃ M : ℤ, ∀ n : ℕ, |(f^[n]) 0| < M :=
  exists.elim (minimal_period_zero_pos_of_not_injective h h0) $
  λ N h1, let g := λ n, |(f^[n]) 0| in
    ⟨extra.seq_max g (N + f.minimal_period (f^[N] 0)) + 1,
    λ n, int.lt_add_one_of_le $ (le_total n N).elim
      (λ h2, extra.le_seq_max_of_le g $ le_add_right h2)
      (λ h2, exists.elim (nat.exists_eq_add_of_le' h2) $ λ c h3,
        by rw [h3, iterate_add_apply, add_comm,
          ← iterate_mod_minimal_period_eq, ← iterate_add_apply];
          exact extra.le_seq_max_of_le g (N.add_le_add_right (c.mod_lt h1).le))⟩

lemma self_mul_map_self_sub_map_neg (a : ℤ) : f^[2 * a.nat_abs ^ 2] 0 = a * (f a - f (-a)) :=
  by rw [mul_sub, sub_eq_add_neg, ← neg_mul, ← h, add_neg_self, int.nat_abs_neg, ← two_mul]

lemma iter_large_map_zero_eq_zero {M : ℤ} (h0 : ∀ n : ℕ, |(f^[n]) 0| < M)
  {a : ℤ} (h1 : M ≤ a) : f.is_periodic_pt (2 * a.nat_abs ^ 2) 0 :=
  int.eq_zero_of_abs_lt_dvd ⟨_, self_mul_map_self_sub_map_neg h a⟩ $ (h0 _).trans_le h1

lemma map_map_zero_of_orbit_zero_bounded (h0 : ∃ M : ℤ, ∀ n : ℕ, |(f^[n]) 0| < M) :
  f.is_periodic_pt 2 0 :=
exists.elim h0 $ λ M h0, suffices (2 * M.nat_abs ^ 2).gcd (2 * (M + 1).nat_abs ^ 2) = 2,
  from cast (congr_arg2 f.is_periodic_pt this rfl) $
    (iter_large_map_zero_eq_zero h h0 $ le_refl M).gcd
    (iter_large_map_zero_eq_zero h h0 $ int.le_add_one $ le_refl M),
(nat.gcd_mul_left 2 _ _).trans $ mul_right_eq_self₀.mpr $ or.inl $
  by rw [← int.nat_abs_pow, ← int.nat_abs_pow, ← int.gcd_eq_nat_abs, int.gcd_eq_one_iff_coprime];
    exact is_coprime.pow ⟨(-1), 1, by rw [one_mul, neg_one_mul, neg_add_cancel_left]⟩

lemma even_of_map_map_zero_eq_zero (h0 : f.is_periodic_pt 2 0) {a : ℤ} (h1 : a ≠ 0) :
  f (-a) = f a :=
  eq.symm $ eq_of_sub_eq_zero $ or.resolve_left
    (mul_eq_zero.mp $ (self_mul_map_self_sub_map_neg h a).symm.trans $
      h0.mul_const $ a.nat_abs ^ 2) h1

lemma map_nonzero_eq_zero (h0 : f.is_periodic_pt 2 0) {a : ℤ} (h1 : a ≠ 0) : f a = 0 :=
begin
  obtain ⟨n, h2⟩ : ∃ n : ℕ, a.nat_abs ^ 2 = n.succ :=
    nat.exists_eq_succ_of_ne_zero (mt nat_abs_sq_eq_zero_imp h1), 
  have h3 := map_iterate_sq h (-a),
  rw [int.nat_abs_neg, h2, iterate_succ_apply, even_of_map_map_zero_eq_zero h h0 h1,
      ← iterate_succ_apply, ← h2, map_iterate_sq h, neg_mul, eq_neg_self_iff, mul_eq_zero] at h3,
  exact h3.resolve_left h1
end

lemma map_eq_zero (h0 : f.is_periodic_pt 2 0) : f = λ _, 0 :=
  funext $ λ a, (ne_or_eq a 0).elim (map_nonzero_eq_zero h h0) $ λ h1, (congr_arg f h1).trans $
    let h2 : (f^[2]) (-2) = -1 * f (-1) + -1 * f (-1) := h (-1) (-1) in
    by rwa [map_neg_one h, mul_zero, add_zero, iterate_succ_apply,
      map_nonzero_eq_zero h h0 (neg_ne_zero.mpr two_ne_zero)] at h2

end solution





/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} : good f ↔ f = (+ 1) ∨ f = λ _, 0 :=
⟨λ h, (em f.injective).imp (eq_add_one_of_injective h)
  (λ h0, map_eq_zero h $ map_map_zero_of_orbit_zero_bounded h $
    orbit_zero_bounded_of_not_injective h h0),
λ h, h.elim (λ h0, cast (congr_arg _ h0.symm) good_add_one)
  (λ h0, cast (congr_arg _ h0.symm) good_zero)⟩ 

end IMO2020A6
end IMOSL
