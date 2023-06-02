import
  IMO2012.A5.case2.A5_case2_comm
  IMO2012.A5.A5_period_quot
  IMO2012.A5.explicit_rings.F2
  IMO2012.A5.explicit_rings.F4
  IMO2012.A5.explicit_rings.F2e

/-! # IMO 2012 A5, Case 2.4: `f(2) = -1` -/

namespace IMOSL
namespace IMO2012A5

section answers

variables (R : Type*) [ring R]

/-- The first respective solution for the subcase. -/
def 𝔽₂_map : 𝔽₂ → R
| 𝔽₂.O := -1
| 𝔽₂.I := 0

theorem case2_4_answer1 : good (𝔽₂_map R)
| 𝔽₂.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₂.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₂_map R) $
    add_comm _ _).trans (zero_mul _).symm

/-- The second respective solution for the subcase. -/
def 𝔽₄_map (φ : R) : 𝔽₄ → R
| 𝔽₄.O := -1
| 𝔽₄.I := 0
| 𝔽₄.X := φ
| 𝔽₄.Y := 1 - φ

theorem case2_4_answer2 {φ : R} (h : φ * (1 - φ) = -1) : good (𝔽₄_map R φ)
| 𝔽₄.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₄.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₄_map R φ) $
    add_comm _ _).trans (zero_mul _).symm
| 𝔽₄.X 𝔽₄.O := (zero_sub φ).trans (mul_neg_one φ).symm
| 𝔽₄.X 𝔽₄.I := (sub_self _).trans (mul_zero φ).symm
| 𝔽₄.X 𝔽₄.X := sub_eq_of_eq_add $ eq_add_of_sub_eq' $ (mul_one_sub φ φ).symm.trans h
| 𝔽₄.X 𝔽₄.Y := (sub_zero (-1)).trans h.symm
| 𝔽₄.Y 𝔽₄.O := (zero_sub _).trans (mul_neg_one _).symm
| 𝔽₄.Y 𝔽₄.I := (sub_self φ).trans (mul_zero _).symm
| 𝔽₄.Y 𝔽₄.X := (sub_zero (-1)).trans $ h.symm.trans $
    (mul_one_sub φ φ).trans (one_sub_mul φ φ).symm
| 𝔽₄.Y 𝔽₄.Y := sub_eq_of_eq_add $ eq_add_of_sub_eq' $
  (one_sub_mul _ _).symm.trans $ (congr_arg (* (1 - φ)) (sub_sub_cancel 1 φ)).trans h

/-- The third respective solution for the subcase. -/
def 𝔽₂ε_map : 𝔽₂ε → R
| 𝔽₂ε.O := -1
| 𝔽₂ε.I := 0
| 𝔽₂ε.X := 1
| 𝔽₂ε.Y := 0

theorem case2_4_answer3 : good (𝔽₂ε_map R)
| 𝔽₂ε.O x := (zero_sub _).trans (neg_one_mul _).symm
| 𝔽₂ε.I x := (sub_eq_zero_of_eq $ congr_arg (𝔽₂ε_map R) $
    add_comm _ _).trans (zero_mul _).symm
| 𝔽₂ε.X 𝔽₂ε.O := (zero_sub 1).trans (one_mul (-1)).symm
| 𝔽₂ε.X 𝔽₂ε.I := (sub_self 0).trans (one_mul 0).symm
| 𝔽₂ε.X 𝔽₂ε.X := (zero_sub (-1)).trans $ (neg_neg 1).trans (one_mul 1).symm
| 𝔽₂ε.X 𝔽₂ε.Y := (sub_self 0).trans (one_mul 0).symm
| 𝔽₂ε.Y 𝔽₂ε.O := (sub_self 0).trans (zero_mul (-1)).symm
| 𝔽₂ε.Y 𝔽₂ε.I := (sub_self 1).trans (zero_mul 0).symm
| 𝔽₂ε.Y 𝔽₂ε.X := (sub_self 0).trans (zero_mul 1).symm
| 𝔽₂ε.Y 𝔽₂ε.Y := (sub_self (-1)).trans (zero_mul 0).symm

end answers




section noncomm_ring

variables {R : Type*} [ring R] (h : (2 : R) = 0)
include h

/-! Some lemmas on rings of characteristic 2 -/
namespace char2

lemma add_self (x : R) : x + x = 0 :=
  (two_mul x).symm.trans (mul_eq_zero_of_left h x)

lemma add_add_cancel (x y : R) : x + y + y = x :=
  (add_assoc x y y).trans $ (congr_arg (has_add.add x) (add_self h y)).trans (add_zero x)

lemma sub_eq_add (x y : R) : x - y = x + y :=
  by rw [sub_eq_iff_eq_add, add_add_cancel h]

lemma add_add_left_cancel (x y : R) : x + (x + y) = y :=
  (add_assoc x x y).symm.trans $ (congr_arg (+ y) (add_self h x)).trans (zero_add y)

lemma add_mul_self {x y : R} (h0 : commute x y) : (x + y) * (x + y) = x * x + y * y :=
  by rw [add_mul, mul_add, mul_add, ← add_assoc, h0.eq, add_add_cancel h]

lemma add_sq {x y : R} (h0 : commute x y) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  (sq $ x + y).trans $ (add_mul_self h h0).trans $ 
    congr_arg2 has_add.add (sq x).symm (sq y).symm

lemma add_one_mul_self (x : R) : (x + 1) * (x + 1) = x * x + 1 :=
  (add_mul_self h $ commute.one_right x).trans $ congr_arg (has_add.add (x * x)) (one_mul 1)

lemma add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 :=
  (add_sq h $ commute.one_right x).trans $ congr_arg (has_add.add $ x ^ 2) (one_pow 2)

lemma pow_add_self_sq (x : R) (n : ℕ) : (x ^ n + x) ^ 2 = (x ^ n) ^ 2 + x ^ 2 :=
  add_sq h (commute.pow_self x n)

end char2



variables {S : Type*} [ring S] [is_domain S] {f : R → S} (h0 : good f)
include h0

private lemma case2_4_lem1 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  by rw [← h0, char2.add_add_left_cancel h, good_map_one h0, sub_zero]

private lemma case2_4_lem2 (x : R) : f ((x + 1) * x + 1) = f (x + 1) * f x :=
  by rw [add_one_mul, ← mul_add_one, case2_4_lem1 h h0];
    exact map_comm_of_comm h0 (comm_self_add_one x)

variables (h1 : f 0 = -1)
include h1

private lemma case2_4_lem3 (x : R) : f (x * x + 1) = f x * f x - 1 :=
  by rw [← h0, char2.add_self h, h1, sub_neg_eq_add, add_sub_cancel]

private lemma case2_4_lem4 (x : R) :
  (f x * f x - 1) * (f x - 1) + f x * f (x + 1) = f (x + 1) * f ((x + 1) * x) :=
begin
  rw [← case2_4_lem3 h h0 h1, ← case2_4_lem1 h h0, ← h0, mul_sub_one, ← add_sub_right_comm],
  refine congr_arg2 has_sub.sub (add_eq_of_eq_sub _) (congr_arg f _),
  rw [← mul_assoc, char2.add_one_mul_self h, mul_add_one, add_right_comm, h0],
  rw [← mul_one_add, add_comm 1 x, char2.add_one_mul_self h]
end

end noncomm_ring



section comm_ring

variables {R S : Type*} [ring R] [comm_ring S] [is_domain S]


section general

private lemma case2_4_lem5_1' (a b : S) :
  a * ((a * a - 1) * (a - 1) + a * b) - b * ((b * b - 1) * (b - 1) + b * a) =
    (a - b) * ((a * a + b * b - 1) * (a + b - 1)) :=
  by ring

private lemma case2_4_lem5_1 {a b : S}
  (h : a * ((a * a - 1) * (a - 1) + a * b) = b * ((b * b - 1) * (b - 1) + b * a)) :
    a = b ∨ (a * a + b * b = 1) ∨ (a + b = 1) :=
  by rwa [← sub_eq_zero, case2_4_lem5_1', mul_eq_zero,
    mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h

private lemma case2_4_lem5_2' (a : S) : a * a * ((a * a - 1) * (a * a - 1)) -
  (((a * a - 1) * (a - 1) + a * a) * ((a * a - 1) * (a - 1) + a * a) - a * a) =
    (1 - (a + a)) * (a * a - 1) :=
  by ring

private lemma case2_4_lem5_2 {a : S} (h : a * a * ((a * a - 1) * (a * a - 1)) =
  (((a * a - 1) * (a - 1) + a * a) * ((a * a - 1) * (a - 1) + a * a) - a * a)) :
  a + a = 1 ∨ a * a = 1 :=
  by rwa [← sub_eq_zero, case2_4_lem5_2', mul_eq_zero,
    sub_eq_zero, sub_eq_zero, eq_comm] at h

variables (h : (2 : R) = 0) {f : R → S} (h0 : good f) (h1 : f 0 = -1)
include h h0 h1

private lemma case2_4_lem5_3 (x : R) :
  f (x + 1) = f x ∨ f (x + 1) * f (x + 1) + f x * f x = 1 ∨ f (x + 1) + f x = 1 :=
begin
  have h2 := case2_4_lem4 h h0 h1 (x + 1),
  rw char2.add_add_cancel h at h2,
  apply case2_4_lem5_1,
  rw [h2, case2_4_lem4 h h0 h1, mul_left_comm, mul_add_one, add_one_mul]
end

private lemma case2_4_lem5_4 {x : R} (h2 : f (x + 1) = f x) :
  f x + f x = 1 ∨ f x * f x = 1 :=
begin
  have h3 := case2_4_lem3 h h0 h1 ((x + 1) * x),
  rw [(comm_self_add_one x).mul_mul_mul_comm, char2.add_one_mul_self h,
      case2_4_lem2 h h0, case2_4_lem3 h h0 h1, ← char2.add_add_cancel h (x * x) 1,
      ← char2.add_one_mul_self h, case2_4_lem3 h h0 h1, h2] at h3,
  replace h3 := congr_arg (has_mul.mul $ f (x + 1) * f (x + 1)) h3,
  rw [mul_sub_one (f _ * _), mul_mul_mul_comm _ _ (f _), ← case2_4_lem4 h h0 h1, h2] at h3,
  exact case2_4_lem5_2 h3
end

private lemma case2_4_lem5 (x : R) :
  f (x + 1) * f (x + 1) + f x * f x = 1 ∨ f (x + 1) + f x = 1 :=
  (case2_4_lem5_3 h h0 h1 x).symm.elim id $ λ h2, or.inr $
  (case2_4_lem5_4 h h0 h1 h2).elim (congr_arg (+ f x) h2).trans $ λ h3, 
begin
  replace h2 := congr_arg2 has_mul.mul h2 h2,
  rw [h3, ← sub_eq_zero, ← case2_4_lem3 h h0 h1,
      char2.add_one_mul_self h, char2.add_add_cancel h] at h2,
  rw [← sub_eq_zero, ← case2_4_lem3 h h0 h1, ← h2] at h3,
  replace h3 := case2_4_lem5_4 h h0 h1 h3,
  rw [h2, add_zero, mul_zero, or_self] at h3,
  exact absurd h3 zero_ne_one
end

end general


section char_S_eq_two

private lemma case2_4_1_lem1 (a b c : S) :
  (a * (b + 1) + c) * (b * (a + 1) + c) - 1 -
    (a * b + c + 1) * ((b + 1) * (a + 1) + (c + 1)) =
  c - (a + b + 1) - 2 * (a * b + 2 * c + 1) :=
  by ring

variables (h : (2 : R) = 0) (h0 : (2 : S) = 0) {f : R → S} (h1 : good f) (h2 : f 0 = -1)
include h h0 h1 h2

private lemma case2_4_1_lem2 (x : R) : f (x + 1) = f x + 1 :=
begin
  rw [← add_left_inj (f x), add_right_comm, char2.add_self h0, zero_add],
  refine (case2_4_lem5 h h1 h2 x).elim (λ h3, _) id,
  rwa [← char2.add_mul_self h0 (commute.all _ _), mul_self_eq_one_iff,
      neg_eq_of_add_eq_zero_right h0, or_self] at h3
end

private lemma case2_4_1_lem3 (x y : R) : f (x * y) = f x * f y + f (x + y) + 1 :=
  by rw [← eq_add_of_sub_eq (h1 x y), case2_4_1_lem2 h h0 h1 h2, char2.add_add_cancel h0]

private lemma case2_4_1_lem4 (x y : R) : f (x * (y + 1)) = f x * (f y + 1) + f (x + y) :=
  by rw [case2_4_1_lem3 h h0 h1 h2, case2_4_1_lem2 h h0 h1 h2, add_assoc, add_right_inj,
    ← add_assoc, case2_4_1_lem2 h h0 h1 h2, char2.add_add_cancel h0]

private lemma case2_4_1_lem5 (x y : R) : f (x + y) = f x + f y + 1 :=
begin
  /- This lemma takes quite long, nearly 0.3s -/
  have h3 := h1 (x * y) ((y + 1) * (x + 1)),
  conv_lhs at h3 { congr,
    rw [← mul_assoc, mul_assoc x, mul_add_one y, ← add_one_mul,
        ← mul_assoc, mul_assoc, eq_add_of_sub_eq (h1 _ _)],
    congr, skip, congr,
    rw [mul_add_one, mul_add_one, add_add_add_comm], skip,
    rw [mul_add_one, add_one_mul, add_assoc, ← add_assoc (x * y),
        ← add_assoc x, ← add_assoc, case2_4_1_lem2 h h0 h1 h2] },
  rw [← sub_sub, add_sub_cancel] at h3,
  iterate 3 { rw case2_4_1_lem4 h h0 h1 h2 at h3 },
  rw [case2_4_1_lem2 h h0 h1 h2, add_right_comm, add_comm y x, case2_4_1_lem3 h h0 h1 h2,
      case2_4_1_lem2 h h0 h1 h2, ← sub_eq_zero, case2_4_1_lem1, h0, zero_mul, sub_zero] at h3,
  exact eq_of_sub_eq_zero h3
end

private lemma case2_4_1_lem4 (x y : R) : f (x * y) + 1 = (f x + 1) * (f y + 1) :=
  by rw [case2_4_1_lem3 h h0 h1 h2, char2.add_add_cancel h0,
    case2_4_1_lem5 h h0 h1 h2, add_assoc, ← add_assoc, ← mul_add_one, ← add_one_mul]

theorem case2_4_1_sol : ∃ φ : R →+* S, f = λ x, φ x - 1 :=
  ⟨⟨λ x, f x + 1,
      add_left_eq_self.mpr (good_map_one h1),
      case2_4_1_lem4 h h0 h1 h2,
      add_eq_zero_iff_eq_neg.mpr h2,
      λ x y, by rw [case2_4_1_lem5 h h0 h1 h2, add_add_add_comm, add_assoc]⟩,
    funext $ λ x, by rw [ring_hom.coe_mk, add_sub_cancel]⟩

end char_S_eq_two


section char_S_ne_two

variables (h : (2 : R) = 0) {f : R → S} (h0 : good f) (h1 : f 0 = -1)
include h h0 h1

private lemma case2_4_2_lem1 (x : R) : f ((x ^ 2) ^ 2) = (f x ^ 2 - 2) * f x ^ 2 :=
  by rw [← char2.add_add_cancel h (x ^ 2) 1, char2.add_one_sq h, sq, case2_4_lem3 h h0 h1,
    sq, case2_4_lem3 h h0 h1, ← sq, ← sq, sub_sq, one_pow, add_sub_cancel, mul_one, sq, ← sub_mul]

variables (h2 : (2 : S) ≠ 0)
include h2

private lemma case2_4_2_lem2 {x : R} (h3 : f (x + 1) ^ 2 + f x ^ 2 = 3) :
  f (x + 1) + f x = 1 ∧ f (x + 1) * f x = -1 :=
begin
  refine (case2_4_lem5 h h0 h1 x).elim (λ h4, absurd h4 _) (λ h4, ⟨h4, _⟩),
  rwa [← sq, ← sq, h3, bit1, add_left_eq_self],
  replace h4 : (f (x + 1) + f x) ^ 2 = 1 ^ 2 := congr_arg (^ 2) h4,
  rwa [one_pow, add_sq', h3, bit1, add_right_comm, add_left_eq_self, mul_assoc, ← mul_one_add,
       mul_eq_zero, or_iff_right h2, add_comm, ← eq_neg_iff_add_eq_zero] at h4
end

private lemma case2_4_2_lem3 (x : R) :
  (f (x + 1) + f x = 1 ∧ f (x + 1) * f x = -1) ∨ f x = 0 ∨ f (x + 1) = 0 :=
begin
  let X := λ x, char2.pow_add_self_sq h x 2,
  let X0 := char2.add_one_sq h,
  let X1 := case2_4_2_lem1 h h0 h1,
  have h3 := case2_4_lem1 h h0 ((x ^ 2) ^ 2),
  rw [mul_add_one, ← sq, ← X, ← X0, ← X0, ← X0, ← X, ← X0, X1, X1, X1] at h3,
  clear X X0 X1,

  rwa [mul_mul_mul_comm, sq x, ← mul_add_one, ← mul_pow,
       case2_4_lem1 h h0, mul_eq_mul_right_iff] at h3,
  revert h3; refine or.imp (λ h4, case2_4_2_lem2 h h0 h1 h2 _)
    (λ h4, mul_eq_zero.mp $ pow_eq_zero h4),
  rwa [mul_sub, sub_mul, ← mul_pow, sub_sub, sub_right_inj, mul_comm, ← add_mul, eq_comm,
       mul_left_eq_self₀, or_iff_left h2, ← add_sub_assoc, sub_eq_iff_eq_add', ← bit1] at h4
end

private lemma case2_4_2_lem4 {x : R} (h3 : f x = 1 ∨ f x = -1) : f (x + 1) = 0 :=
  (case2_4_2_lem3 h h0 h1 h2 x).symm.elim
    (λ h4, h4.resolve_left $ h3.elim (λ h5, ne_of_eq_of_ne h5 one_ne_zero)
      (λ h5, ne_of_eq_of_ne h5 $ neg_ne_zero.mpr one_ne_zero))
    (λ h4, h3.elim (λ h5, by rw [h5, add_left_eq_self] at h4; exact h4.1)
      (λ h5, by rw [h5, mul_neg_one, neg_inj, add_neg_eq_iff_eq_add] at h4;
        exact absurd (add_right_eq_self.mp $ h4.1.symm.trans h4.2) one_ne_zero))

private lemma case2_4_2_lem5 {x : R} (h3 : f x = 0) : f (x + 1) = 1 ∨ f (x + 1) = -1 :=
begin
  have h4 := case2_4_lem5 h h0 h1 x,
  rw [h3, mul_zero, add_zero, add_zero, mul_self_eq_one_iff] at h4,
  exact h4.elim id or.inl
end

private lemma case2_4_2_lem6 (x : R) : (f (x + 1) + f x = 1 ∧ f (x + 1) * f x = -1) ∨
  f x = 0 ∨ f x = 1 ∨ f x = -1 :=
  (case2_4_2_lem3 h h0 h1 h2 x).imp id $ or.imp id $
    λ h5, by rw ← char2.add_add_cancel h x 1; exact case2_4_2_lem5 h h0 h1 h2 h5

private lemma case2_4_2_lem7 {x y : R} (h3 : f x = -f y) : f x = 0 ∨ f x = 1 ∨ f x = -1 :=
  (case2_4_2_lem6 h h0 h1 h2 x).symm.elim id $ λ h4,
begin
  rw [h3, neg_eq_zero, neg_inj, neg_eq_iff_eq_neg, or_comm (f y = -1)],
  refine (case2_4_2_lem6 h h0 h1 h2 y).elim (λ h5, _) id,
  rw [h3, mul_neg, ← h5.2, neg_eq_iff_add_eq_zero, ← add_mul, mul_eq_zero] at h4,
  refine h4.2.symm.imp id (λ h6, _),
  rw [eq_add_of_add_neg_eq h4.1, add_assoc, add_comm (f y), h5.1] at h6,
  exact absurd h6 h2
end



section map_eq_one

variables {c : R} (h3 : f c = 1)
include h3

private lemma case2_4_2_1_lem1 (y : R) : f (c * y + 1) = f (c + y) + f y :=
  (eq_add_of_sub_eq' $ h0 c y).trans $ by rw [h3, one_mul]

private lemma case2_4_2_1_lem2 (y : R) : f (c * (c + y) + 1) = f (c * y + 1) :=
  let h4 := case2_4_2_1_lem1 h h0 h1 h2 h3 in
    by rw [h4, h4, char2.add_add_left_cancel h, add_comm]

private lemma case2_4_2_1_lem3 : f (c + 1) = 0 :=
  case2_4_2_lem4 h h0 h1 h2 (or.inl h3)

private lemma case2_4_2_1_lem4 : f (c * c) = -1 :=
  by rw [← char2.add_add_cancel h (c * c) 1, ← char2.add_one_mul_self h,
    case2_4_lem3 h h0 h1, sub_eq_neg_self, mul_self_eq_zero];
  exact case2_4_2_1_lem3 h h0 h1 h2 h3

variables (h4 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h4

private lemma case2_4_2_1_lem5 : c * (c * c) = 0 :=
  h4 (c * (c * c)) $ λ y,
begin
  let X := char2.add_add_cancel h,
  replace h4 := h0 (c * c + (c + 1)) (c + 1),
  rw [case2_4_2_1_lem3 h h0 h1 h2 h3, mul_zero, X, case2_4_2_1_lem4 h h0 h1 h2 h3,
      sub_eq_zero, ← add_assoc, ← mul_add_one, add_one_mul, mul_assoc,
      char2.add_one_mul_self h, mul_add_one, ← add_assoc, X, X] at h4,
  rw [← add_neg_eq_zero, ← neg_one_mul, ← h4, ← eq_add_of_sub_eq' (h0 _ _),
      mul_assoc, ← case2_4_2_1_lem2 h h0 h1 h2 h3, add_comm c, mul_assoc,
      ← mul_add_one, ← mul_assoc, eq_add_of_sub_eq (h0 _ _), ← add_assoc,
      case2_4_2_1_lem4 h h0 h1 h2 h3, neg_one_mul, neg_add_eq_zero, ← mul_add],
  exact (case2_4_2_1_lem2 h h0 h1 h2 h3 y).symm
end

private lemma case2_4_2_1_lem6 : c * c = 0 :=
  h4 (c * c) $ λ y,
begin
  have h5 : ∀ t : R, f (c * c * t + 1) = f (c * c + t) - f t :=
    λ t, by rw [eq_add_of_sub_eq' (h0 _ _), sub_eq_add_neg,
      case2_4_2_1_lem4 h h0 h1 h2 h3, neg_one_mul],
  rw [← sub_eq_zero, ← h5],
  have h6 := h5 (c * c + y),
  rwa [char2.add_add_left_cancel h, ← neg_sub, ← h5, mul_add, mul_assoc,
       eq_neg_iff_add_eq_zero, case2_4_2_1_lem5 h h0 h1 h2 h3 h4, mul_zero,
       zero_add, ← two_mul, mul_eq_zero, or_iff_right h2] at h6
end

private lemma case2_4_2_1_lem7 : c ≠ 0 :=
  λ h5, h2 $ add_eq_zero_iff_eq_neg.mpr $ by rw [← h1, ← h3, h5]

private lemma case2_4_2_1_lem8 (y : R) : f (c * y + 1) ≠ 1 :=
  λ h5, case2_4_2_1_lem7 h h0 h1 h2 h3 h4 $
    by replace h5 := mul_eq_zero_of_right c (case2_4_2_1_lem6 h h0 h1 h2 h5 h4);
    rwa [char2.add_one_mul_self h, mul_add_one, ← mul_assoc, ← mul_assoc c,
      case2_4_2_1_lem6 h h0 h1 h2 h3 h4, zero_mul, zero_mul, zero_add] at h5

private theorem case2_4_2_1_thm (y : R) : f (c * y + 1) = 0 :=
begin
  have h5 := h0 c (c * y + 1),
  rw [h3, one_mul, mul_add_one, ← mul_assoc, case2_4_2_1_lem6 h h0 h1 h2 h3 h4, zero_mul,
      zero_add, case2_4_2_1_lem3 h h0 h1 h2 h3, zero_sub, ← add_assoc, ← mul_one_add] at h5,
  refine (case2_4_2_lem7 h h0 h1 h2 h5.symm).resolve_right
    (λ h6, h6.elim (case2_4_2_1_lem8 h h0 h1 h2 h3 h4 y) (λ h7, _)),
  rw [h7, neg_inj] at h5; exact case2_4_2_1_lem8 h h0 h1 h2 h3 h4 (1 + y) h5
end

end map_eq_one



section map_ne_one

variables (h3 : ∀ x, f x ≠ 1)
include h3

private lemma case2_4_2_2_lem1 {x y : R} (h4 : f x = -f y) : f x = 0 :=
  (case2_4_2_lem7 h h0 h1 h2 h4).resolve_right $ λ h5, h5.elim (h3 x) $
    λ h6, by rw [h6, neg_inj] at h4; exact h3 y h4.symm

variables (h4 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h4

private lemma case2_4_2_2_lem2 {c : R} (h5 : f c = -1) : c = 0 :=
  h4 c $ λ y,
begin
  have h6 : ∀ t : R, f (c * t + 1) = f (c + t) - f t :=
    λ t, by rw [eq_add_of_sub_eq' (h0 _ _), h5, neg_one_mul, sub_eq_add_neg],
  rw [← sub_eq_zero, ← h6],
  replace h5 := h6 (c + y),
  rw [char2.add_add_left_cancel h, ← neg_sub, ← h6, ← neg_eq_iff_eq_neg] at h5,
  exact case2_4_2_2_lem1 h h0 h1 h2 h3 h5.symm
end

private lemma case2_4_2_2_lem3 {c : R} (h5 : f c = 0) : c = 1 :=
  (case2_4_2_lem5 h h0 h1 h2 h5).elim (λ h6, absurd h6 $ h3 _) $
    λ h6, by rw [← char2.add_add_cancel h c 1, case2_4_2_2_lem2 h h0 h1 h2 h3 h4 h6, zero_add]

private theorem case2_4_2_2_thm1 {c : R}
  (h5 : ¬(f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1)) : c = 0 ∨ c = 1 :=
  or.symm $ (case2_4_2_lem6 h h0 h1 h2 c).elim (λ h6, absurd h6 h5) $
    λ h6, h6.imp (case2_4_2_2_lem3 h h0 h1 h2 h3 h4) $
      λ h7, h7.elim (λ h8, absurd h8 $ h3 c) (case2_4_2_2_lem2 h h0 h1 h2 h3 h4)

private lemma case2_4_2_2_lem4 {c : R} (h5 : f (c + 1) * f c = -1) : c * c + c = 1 :=
  by rw [← char2.add_add_cancel h (c * c + c) 1, add_left_eq_self, ← add_one_mul];
    exact case2_4_2_2_lem2 h h0 h1 h2 h3 h4 ((case2_4_lem2 h h0 c).trans h5)

private theorem case2_4_2_2_thm2 {c : R} (h5 : f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1)
  (x : R) : (x = 0 ∨ x = 1) ∨ (x = c ∨ x = c + 1) :=
  (em' _).imp (case2_4_2_2_thm1 h h0 h1 h2 h3 h4) $ λ h6,
begin
  rw [← sub_eq_zero, ← sub_eq_iff_eq_add', char2.sub_eq_add h],
  refine case2_4_2_2_thm1 h h0 h1 h2 h3 h4 (λ h7, _),
  replace h5 := case2_4_2_2_lem4 h h0 h1 h2 h3 h4 h5.2,
  replace h6 := case2_4_2_2_lem4 h h0 h1 h2 h3 h4 h6.2,
  replace h7 := case2_4_2_2_lem4 h h0 h1 h2 h3 h4 h7.2,
  rw [add_mul, mul_add, mul_add, add_assoc, add_add_add_comm _ _ x, h5,
      add_add_add_comm, ← add_assoc, add_left_eq_self, ← add_assoc,
      add_right_comm _ _ x, h6, add_assoc, ← char2.add_self h 1, add_right_inj] at h7,
  replace h4 := congr_arg (has_mul.mul c) h7,
  rw [mul_one, mul_add, add_comm, ← mul_assoc, ← mul_assoc] at h4,
  nth_rewrite 4 ← one_mul c at h4,
  rw [← eq_sub_iff_add_eq, char2.sub_eq_add h] at h5,
  rw [← h7, add_mul, add_right_inj, mul_assoc x, h5,
      mul_one_add, one_add_mul, add_right_inj] at h4,
  rw [h4, char2.add_self h] at h7,
  rw [h7, good_map_one h0, zero_eq_neg] at h1,
  exact one_ne_zero h1
end

end map_ne_one

end char_S_ne_two

end comm_ring





section solution

variables {R : Type*} [comm_ring R] (h : (2 : R) = 0)
include h

private def case2_4_𝔽₂_hom : 𝔽₂ →+* R :=
  𝔽₂.cast_hom h

variables {S : Type*} [comm_ring S] [is_domain S] {f : R → S} (h0 : good f)
include h0

private lemma case2_4_lift_two_eq_zero : (2 : R ⧸ period_ideal h0) = 0 :=
  congr_arg (ideal.quotient.mk $ period_ideal h0) h

variables (h1 : f 0 = -1)
include h1



section char_S_ne_two

variables (h2 : (2 : S) ≠ 0)
include h2


section construction

variables (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
include h3


section 𝔽₂ε

variables {c : R} (h4 : f c = 1)
include h4

private def case2_4_𝔽₂ε_hom : 𝔽₂ε →+* R :=  
  𝔽₂ε.cast'_hom h (case2_4_2_1_lem6 h h0 h1 h2 h4 h3)

private lemma case2_4_𝔽₂ε_hom_surjective' : ∀ x, (x = 0 ∨ x = c) ∨ (x = 1 ∨ x = c + 1) :=
  cases_of_nonperiod_quasi_period h0 h3 h1
    (case2_4_2_1_thm h h0 h1 h2 h4 h3) (case2_4_2_1_lem7 h h0 h1 h2 h4 h3)

private lemma case2_4_𝔽₂ε_hom_bijective :
  function.bijective (case2_4_𝔽₂ε_hom h h0 h1 h2 h3 h4) :=
  ⟨𝔽₂ε.cast'_hom_injective h _ (case2_4_2_1_lem7 h h0 h1 h2 h4 h3),
  λ x, (case2_4_𝔽₂ε_hom_surjective' h h0 h1 h2 h3 h4 x).elim
    (λ h5, h5.elim (λ h6, ⟨𝔽₂ε.O, h6.symm⟩) (λ h6, ⟨𝔽₂ε.X, h6.symm⟩))
    (λ h5, h5.elim (λ h6, ⟨𝔽₂ε.I, h6.symm⟩) (λ h6, ⟨𝔽₂ε.Y, h6.symm⟩))⟩

private noncomputable def case2_4_𝔽₂ε_equiv : 𝔽₂ε ≃+* R :=
  ring_equiv.of_bijective _ (case2_4_𝔽₂ε_hom_bijective h h0 h1 h2 h3 h4)

private lemma case2_4_quotient_𝔽₂ε_sol' :
  ∀ x : 𝔽₂ε, f (case2_4_𝔽₂ε_equiv h h0 h1 h2 h3 h4 x) = 𝔽₂ε_map S x
| 𝔽₂ε.O := h1
| 𝔽₂ε.I := good_map_one h0
| 𝔽₂ε.X := h4
| 𝔽₂ε.Y := case2_4_2_1_lem3 h h0 h1 h2 h4

private lemma case2_4_quotient_𝔽₂ε_sol :
  f = 𝔽₂ε_map S ∘ (case2_4_𝔽₂ε_equiv h h0 h1 h2 h3 h4).symm :=
  let φ := case2_4_𝔽₂ε_equiv h h0 h1 h2 h3 h4 in
  funext $ λ x, (congr_arg f (φ.apply_symm_apply x).symm).trans $
    case2_4_quotient_𝔽₂ε_sol' h h0 h1 h2 h3 h4 $ φ.symm x

end 𝔽₂ε


section 𝔽₂

variables (h4 : ∀ x, f x ≠ 1) (h5 : ∀ c, ¬(f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1))
include h4 h5

private lemma case2_4_𝔽₂_hom_bijective :
  function.bijective (case2_4_𝔽₂_hom h) :=
  ⟨𝔽₂.cast_hom_injective h (one_ne_zero_of_map_zero h0 h1),
  λ x, (case2_4_2_2_thm1 h h0 h1 h2 h4 h3 $ h5 x).elim
    (λ h6, ⟨𝔽₂.O, h6.symm⟩) (λ h6, ⟨𝔽₂.I, h6.symm⟩)⟩

private noncomputable def case2_4_𝔽₂_equiv : 𝔽₂ ≃+* R :=
  ring_equiv.of_bijective _ (case2_4_𝔽₂_hom_bijective h h0 h1 h2 h3 h4 h5)

private lemma case2_4_quotient_𝔽₂_sol' :
  ∀ x : 𝔽₂, f (case2_4_𝔽₂_equiv h h0 h1 h2 h3 h4 h5 x) = 𝔽₂_map S x
| 𝔽₂.O := h1
| 𝔽₂.I := good_map_one h0

private lemma case2_4_quotient_𝔽₂_sol :
  f = 𝔽₂_map S ∘ (case2_4_𝔽₂_equiv h h0 h1 h2 h3 h4 h5).symm :=
  let φ := case2_4_𝔽₂_equiv h h0 h1 h2 h3 h4 h5 in
  funext $ λ x, (congr_arg f (φ.apply_symm_apply x).symm).trans $
    case2_4_quotient_𝔽₂_sol' h h0 h1 h2 h3 h4 h5 $ φ.symm x

end 𝔽₂


section 𝔽₄

variables (h4 : ∀ x, f x ≠ 1) {c : R} (h5 : f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1)
include h4 h5

private def case2_4_𝔽₄_hom : 𝔽₄ →+* R :=
  𝔽₄.cast'_hom h (case2_4_2_2_lem4 h h0 h1 h2 h4 h3 h5.2)

private lemma case2_4_𝔽₄_hom_bijective :
  function.bijective (case2_4_𝔽₄_hom h h0 h1 h2 h3 h4 h5) :=
  ⟨𝔽₄.cast'_hom_injective h _ (one_ne_zero_of_map_zero h0 h1),
  λ x, (case2_4_2_2_thm2 h h0 h1 h2 h4 h3 h5 x).elim
    (λ h6, h6.elim (λ h7, ⟨𝔽₄.O, h7.symm⟩) (λ h7, ⟨𝔽₄.I, h7.symm⟩))
    (λ h6, h6.elim (λ h7, ⟨𝔽₄.X, h7.symm⟩) (λ h7, ⟨𝔽₄.Y, h7.symm⟩))⟩

private noncomputable def case2_4_𝔽₄_equiv : 𝔽₄ ≃+* R :=
  ring_equiv.of_bijective _ (case2_4_𝔽₄_hom_bijective h h0 h1 h2 h3 h4 h5)

private lemma case2_4_quotient_𝔽₄_sol' :
  ∀ x : 𝔽₄, f (case2_4_𝔽₄_equiv h h0 h1 h2 h3 h4 h5 x) = 𝔽₄_map S (f c) x
| 𝔽₄.O := h1
| 𝔽₄.I := good_map_one h0
| 𝔽₄.X := rfl
| 𝔽₄.Y := eq_sub_of_add_eq h5.1

private lemma case2_4_quotient_𝔽₄_sol :
  f = 𝔽₄_map S (f c) ∘ (case2_4_𝔽₄_equiv h h0 h1 h2 h3 h4 h5).symm :=
  let φ := case2_4_𝔽₄_equiv h h0 h1 h2 h3 h4 h5 in
  funext $ λ x, (congr_arg f (φ.apply_symm_apply x).symm).trans $
    case2_4_quotient_𝔽₄_sol' h h0 h1 h2 h3 h4 h5 $ φ.symm x

end 𝔽₄

end construction


private lemma case2_4_𝔽₂ε_lift_decomp (h3 : ∃ c, f c = 1) :
  ∃ φ : R ⧸ period_ideal h0 ≃+* 𝔽₂ε, period_lift h0 = 𝔽₂ε_map S ∘ φ :=
    exists.elim h3 $ λ c h4, let h5 : period_lift h0 (ideal.quotient.mk _ c) = 1 := h4 in
  ⟨_, case2_4_quotient_𝔽₂ε_sol (case2_4_lift_two_eq_zero h h0) (period_lift_is_good h0)
    h1 h2 (zero_of_periodic_period_lift h0) h5⟩

private theorem case2_4_𝔽₂ε_sol (h3 : ∃ c, f c = 1) :
  ∃ φ : R →+* 𝔽₂ε, function.surjective φ ∧ f = 𝔽₂ε_map S ∘ φ :=
  exists.elim (case2_4_𝔽₂ε_lift_decomp h h0 h1 h2 h3) $
    λ ψ h4, let π := ideal.quotient.mk (period_ideal h0) in
    ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h0).symm.trans $ congr_arg (∘ π) h4⟩

private lemma case2_4_𝔽₂_lift_decomp (h3 : ∀ x, f x ≠ 1)
  (h4 : ∀ c, ¬(f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1)) :
  ∃ φ : R ⧸ period_ideal h0 ≃+* 𝔽₂, period_lift h0 = 𝔽₂_map S ∘ φ :=
  ⟨_, case2_4_quotient_𝔽₂_sol (case2_4_lift_two_eq_zero h h0) (period_lift_is_good h0) h1 h2
    (zero_of_periodic_period_lift h0) (λ x, quot.induction_on x h3) (λ c, quot.induction_on c h4)⟩

private theorem case2_4_𝔽₂_sol (h3 : ∀ x, f x ≠ 1)
  (h4 : ∀ c, ¬(f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1)) :
  ∃ φ : R →+* 𝔽₂, function.surjective φ ∧ f = 𝔽₂_map S ∘ φ :=
  exists.elim (case2_4_𝔽₂_lift_decomp h h0 h1 h2 h3 h4) $
    λ ψ h5, let π := ideal.quotient.mk (period_ideal h0) in
    ⟨ψ.to_ring_hom.comp π, (equiv_like.surjective ψ).comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h0).symm.trans $ congr_arg (∘ π) h5⟩

private lemma case2_4_𝔽₄_lift_decomp (h3 : ∀ x, f x ≠ 1)
  (h4 : ∃ c, f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1) :
  ∃ (φ : R ⧸ period_ideal h0 ≃+* 𝔽₄) (s : S), period_lift h0 = 𝔽₄_map S s ∘ φ :=
  exists.elim h4 $ λ c h5, let c' := ideal.quotient.mk (period_ideal h0) c,
    f' := period_lift h0, h6 : f' (c' + 1) + f' c' = 1 ∧ f' (c' + 1) * f' c' = -1 := h5 in
  ⟨_, f c, case2_4_quotient_𝔽₄_sol (case2_4_lift_two_eq_zero h h0) (period_lift_is_good h0) h1 h2
    (zero_of_periodic_period_lift h0) (λ x, quot.induction_on x h3) h6⟩

private theorem case2_4_𝔽₄_sol (h3 : ∀ x, f x ≠ 1)
  (h4 : ∃ c, f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1) :
  ∃ (φ : R →+* 𝔽₄) (s : S), function.surjective φ ∧ f = 𝔽₄_map S s ∘ φ :=
  exists.elim (case2_4_𝔽₄_lift_decomp h h0 h1 h2 h3 h4) $
    λ ψ h5, exists.elim h5 $ λ s h6, let π := ideal.quotient.mk (period_ideal h0) in
    ⟨ψ.to_ring_hom.comp π, s, (equiv_like.surjective ψ).comp π.is_surjective,
      (period_lift_comp_quotient_eq_f h0).symm.trans $ congr_arg (∘ π) h6⟩

end char_S_ne_two





theorem case2_4_sol :
  (∃ φ : R →+* S, f = λ x, φ x - 1) ∨
  (∃ φ : R →+* 𝔽₂ε, function.surjective φ ∧ f = 𝔽₂ε_map S ∘ φ) ∨
  (∃ φ : R →+* 𝔽₂, function.surjective φ ∧ f = 𝔽₂_map S ∘ φ) ∨ 
  (∃ (φ : R →+* 𝔽₄) (s : S), function.surjective φ ∧ f = 𝔽₄_map S s ∘ φ) :=
  (eq_or_ne (2 : S) 0).imp (λ h2, case2_4_1_sol h h2 h0 h1) $
    λ h2, (em $ ∃ c, f c = 1).imp (case2_4_𝔽₂ε_sol h h0 h1 h2) $
      λ h3, let h4 := forall_not_of_not_exists h3 in
      (em $ ∃ c, f (c + 1) + f c = 1 ∧ f (c + 1) * f c = -1).symm.imp
        (λ h5, case2_4_𝔽₂_sol h h0 h1 h2 h4 $ forall_not_of_not_exists h5)
        (case2_4_𝔽₄_sol h h0 h1 h2 h4)

end solution

end IMO2012A5
end IMOSL
