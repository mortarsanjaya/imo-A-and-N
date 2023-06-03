import data.int.interval

/-! # IMO 2014 A4 -/

namespace IMOSL
namespace IMO2014A4

def good (b c : ℤ) (f : ℤ → ℤ) :=
  ∀ x y : ℤ, f (y + f x) - f y = f (b * x) - f x + c



/-- Given `b k : ℤ` with `k ≠ 0`, there exists `m ≠ n` such that `b^m ≡ b^n (mod k)`. -/
lemma exists_ne_pow_eq {k : ℤ} (h : k ≠ 0) (b : ℤ) :
  ∃ m n : ℕ, m ≠ n ∧ b ^ m % k = b ^ n % k :=
begin
  /- Over 0.1s; too slow -/
  have h0 : set.maps_to (λ (x : ℕ), b ^ x % k) set.univ (finset.Ico 0 $ |k|) :=
    λ x _, by rw [finset.coe_Ico, set.mem_Ico];
      exact ⟨(b ^ x).mod_nonneg h, (b ^ x).mod_lt h⟩,
  obtain ⟨m, -, n, -, h, h0⟩ : ∃ (m : ℕ) (H : m ∈ (set.univ : set ℕ)) (n : ℕ) (H : n ∈ (set.univ : set ℕ)),
    m ≠ n ∧ b ^ m % k = b ^ n % k :=
    set.infinite_univ.exists_ne_map_eq_of_maps_to h0 (set.to_finite _),
  exact ⟨m, n, h, h0⟩
end



/-! The solution to the main problem starts here. -/
lemma linear_good' (k m : ℤ) : good (k + 1) (k * m) (λ x, k * x + m) :=
  λ x y, by rw [add_sub_add_right_eq_sub, mul_add, add_sub_cancel',
    add_sub_add_right_eq_sub, add_one_mul, ← mul_sub, add_sub_cancel, ← mul_add]

lemma linear_good {b c : ℤ} (h : b - 1 ∣ c) : good b c (λ x, (b - 1) * x + c / (b - 1)) :=
begin
  cases h with k h,
  cases eq_or_ne (b - 1) 0 with h0 h0,
  { rw [h, h0, int.div_zero, zero_mul],
    conv { congr, skip, skip, funext, rw [zero_mul, zero_add] },
    exact λ x y, (add_zero _).symm },
  { nth_rewrite 0 ← sub_add_cancel b 1,
    rw [h, int.mul_div_cancel_left _ h0],
    exact linear_good' (b - 1) k } 
end



section good_lemmas

variables {b c : ℤ} {f : ℤ → ℤ} (h : good b c f)
include h

lemma map_map_zero_add (y : ℤ) : f (y + f 0) = f y + c :=
  eq_add_of_sub_eq' $ by rw [h, mul_zero, sub_self, zero_add]

lemma map_mul_map_zero_add (k y : ℤ) : f (y + f 0 * k) = f y + c * k :=
  int.induction_on k
    ((congr_arg f $ add_right_eq_self.mpr $ mul_zero _).trans $
      self_eq_add_right.mpr $ mul_zero _)
    (λ i h0, by rw [mul_add_one, ← add_assoc,
      map_map_zero_add h, h0, add_assoc, ← mul_add_one])
    (λ i h0, by rwa [mul_sub_one c, ← add_sub_assoc, eq_sub_iff_add_eq,
      ← map_map_zero_add h, add_assoc, ← mul_add_one, sub_add_cancel])

lemma map_b_mul_eq_of_map_eq {x y : ℤ} (h0 : f x = f y) : f (b * x) = f (b * y) :=
  by have h1 := h y 0; rwa [← h0, h, add_left_inj, sub_left_inj] at h1

lemma map_b_pow_mul_eq_of_map_eq {x y : ℤ} (h0 : f x = f y) :
  ∀ k : ℕ, f (b ^ k * x) = f (b ^ k * y)
| 0 := by rwa [pow_zero, one_mul, one_mul]
| (k+1) := by rw [pow_succ, mul_assoc, mul_assoc];
  exact map_b_mul_eq_of_map_eq h (map_b_pow_mul_eq_of_map_eq k)

variables (h0 : 1 < b.nat_abs) (h1 : c ≠ 0)
include h0 h1

lemma map_inj {x y : ℤ} (h2 : f x = f y) : x = y :=
begin
  have h3 : f 0 ≠ 0 := λ h3, h1 (by rw [← zero_add c, ← h3,
    ← map_map_zero_add h, h3, zero_add, h3]),
  obtain ⟨m, n, h4, h5⟩ := exists_ne_pow_eq h3 b,
  revert h4; apply or.resolve_right,
  rw [int.mod_eq_mod_iff_mod_sub_eq_zero, ← int.dvd_iff_mod_eq_zero] at h5,
  cases h5 with N h5,
  
  have h4 := map_b_pow_mul_eq_of_map_eq h h2 m,
  rw [eq_add_of_sub_eq' h5, add_mul, mul_assoc, map_mul_map_zero_add h, add_mul,
      mul_assoc, map_mul_map_zero_add h, map_b_pow_mul_eq_of_map_eq h h2,
      add_right_inj, mul_eq_mul_left_iff, or_iff_left h1, mul_eq_mul_left_iff] at h4,
  revert h4; refine or.imp id (λ h4, _),
  rw [h4, mul_zero, sub_eq_zero] at h5,
  exact int.pow_right_injective h0 h5
end

lemma map_is_linear' (x : ℤ) : f x = (b - 1) * x + f 0 :=
begin
  rw [sub_one_mul, ← add_sub_right_comm, eq_sub_iff_add_eq'],
  apply map_inj h h0 h1,
  rw [map_map_zero_add h, eq_add_of_sub_eq (h _ _), add_right_comm, sub_add_cancel]
end

lemma map_zero_eq : c = (b - 1) * f 0 :=
  by rw [← add_right_inj (f 0), ← map_map_zero_add h, zero_add, add_comm];
    exact map_is_linear' h h0 h1 (f 0)

lemma map_is_linear (x : ℤ) : f x = (b - 1) * x + c / (b - 1) :=
  (map_is_linear' h h0 h1 x).trans $ congr_arg (has_add.add _) $
    int.eq_div_of_mul_eq_right
      (λ h2, ne_of_gt h0 $ congr_arg int.nat_abs $ eq_of_sub_eq_zero h2)
      (map_zero_eq h h0 h1).symm

end good_lemmas





section solution

variables {b c : ℤ} (h : 1 < b.nat_abs) (h0 : c ≠ 0)
include h h0

/-- Final solution, Case 1: `b - 1 ∤ c` -/
theorem final_solution_case1 (h1 : ¬b - 1 ∣ c) {f : ℤ → ℤ} : ¬good b c f :=
  λ h2, h1 ⟨f 0, map_zero_eq h2 h h0⟩

/-- Final solution, Case 2: `b - 1 ∣ c` -/
theorem final_solution_case2 (h1 : b - 1 ∣ c) {f : ℤ → ℤ} :
  good b c f ↔ f = λ x, (b - 1) * x + c / (b - 1) :=
  ⟨λ h2, funext $ map_is_linear h2 h h0,
  λ h2, cast (congr_arg (good b c) h2.symm) (linear_good h1)⟩

end solution

end IMO2014A4
end IMOSL
