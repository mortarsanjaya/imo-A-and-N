import logic.relation algebra.big_operators.multiset.basic data.nat.parity data.nat.log

/-! # IMO 2022 C6, Basic File (Legal Moves) -/

namespace IMOSL
namespace IMO2022C6

/-
set_option profiler true
set_option profiler.threshold 0.05
-/

open function relation multiset

/- ### Extra lemmas -/

lemma multiset_exists_map_mul_of_dvd_all {m : ℕ} {X : multiset ℕ} :
  (∀ x : ℕ, x ∈ X → m ∣ x) → ∃ Y : multiset ℕ, X = Y.map (has_mul.mul m) :=
  multiset.induction_on X (λ _, ⟨0, rfl⟩) $
    λ a X h h0, exists.elim (h $ λ x h1, h0 x $ mem_cons_of_mem h1) $
    λ Y h, exists.elim (h0 a $ mem_cons_self a X) $
    λ c h1, ⟨c ::ₘ Y, (congr_arg2 _ h1 h).trans (Y.map_cons _ _).symm⟩

lemma odd_coprime_two {m : ℕ} (h : odd m) : m.coprime 2 :=
  by rw [nat.coprime, nat.gcd_comm, nat.gcd_rec, nat.odd_iff.mp h, nat.gcd_one_left]

lemma odd_dvd_two_mul_imp_dvd {m : ℕ} (h : odd m) {c : ℕ} (h0 : m ∣ 2 * c) : m ∣ c :=
  (odd_coprime_two h).dvd_of_dvd_mul_left h0





/- ### Legal moves: `legal_op` and its properties -/

inductive legal_op : multiset ℕ → multiset ℕ → Prop
| move_pebble (a b c : ℕ) (X : multiset ℕ) :
    legal_op ((a + c) ::ₘ (b + c) ::ₘ X) (a ::ₘ b ::ₘ (2 * c) ::ₘ X)
| remove_zero (X : multiset ℕ) :
    legal_op (0 ::ₘ X) X

namespace legal_op

@[protected]
theorem induction {P : multiset ℕ → multiset ℕ → Prop}
  (h : ∀ (a b c : ℕ) (X : multiset ℕ),
    P ((a + c) ::ₘ (b + c) ::ₘ X) (a ::ₘ b ::ₘ (2 * c) ::ₘ X))
  (h0 : ∀ X : multiset ℕ, P (0 ::ₘ X) X) :
  ∀ A B : multiset ℕ, legal_op A B → P A B :=
  λ A B h1, h1.rec_on h h0

theorem add_right (A : multiset ℕ) :
  ∀ {B C : multiset ℕ}, legal_op B C → legal_op (B + A) (C + A) := 
induction
(λ a b c X, by iterate 5 { rw cons_add }; exact move_pebble a b c (X + A))
(λ X, (cons_add 0 X A).symm ▸ remove_zero (X + A))

theorem add_left (A : multiset ℕ) {B C : multiset ℕ} (h : legal_op B C) :
  legal_op (A + B) (A + C) := 
  add_comm B A ▸ add_comm C A ▸ add_right A h

theorem cons_congr (a : ℕ) {B C : multiset ℕ} (h : legal_op B C) :
  legal_op (a ::ₘ B) (a ::ₘ C) := 
  add_left {a} h

theorem map_mul_left (m : ℕ) : ∀ {A B : multiset ℕ}, legal_op A B →
  legal_op (A.map $ has_mul.mul m) (B.map $ has_mul.mul m) :=
induction
(λ a b c X, by iterate 5 { rw map_cons }; rw [mul_left_comm, mul_add, mul_add];
  exact move_pebble (m * a) (m * b) (m * c) _)
(λ X, (X.map_cons (has_mul.mul m) 0).symm ▸ remove_zero _)

theorem sum_eq : ∀ {A B : multiset ℕ}, legal_op A B → A.sum = B.sum :=
induction
(λ a b c X, by iterate 5 { rw sum_cons };
  rw [← add_assoc, add_add_add_comm, ← two_mul, add_assoc, add_assoc])
(λ X, (sum_cons 0 X).trans $ zero_add X.sum)



theorem succ_two_to_self_two_one (n : ℕ) (X : multiset ℕ) :
  legal_op (n.succ ::ₘ 2 ::ₘ X) (n ::ₘ 2 ::ₘ 1 ::ₘ X) :=
  cons_swap 1 2 X ▸ move_pebble n 1 1 X

theorem exists_two_cons_right {X : multiset ℕ} (h : ∀ a, a ∈ X → a ≠ 0) (h0 : 1 < X.card) :
  ∃ Y : multiset ℕ, legal_op X (2 ::ₘ Y) :=
begin
  cases exists_mem_of_ne_zero (card_pos.mp $ pos_of_gt h0) with a h1,
  obtain ⟨X, rfl⟩ := exists_cons_of_mem h1,
  obtain ⟨a, rfl⟩ := nat.exists_eq_succ_of_ne_zero (h a h1),
  rw [card_cons, nat.succ_lt_succ_iff, card_pos] at h0,
  cases exists_mem_of_ne_zero h0 with b h2,
  obtain ⟨X, rfl⟩ := exists_cons_of_mem h2,
  obtain ⟨b, rfl⟩ := nat.exists_eq_succ_of_ne_zero (h b $ mem_cons_of_mem h2),
  refine ⟨a ::ₘ b ::ₘ X, cast (congr_arg2 _ rfl _) (move_pebble a b 1 X)⟩,
  rw [cons_swap 2, cons_swap 2, nat.mul_one]
end



theorem odd_dvd_all_left_of_right {m : ℕ} (h : odd m) : ∀ {A B : multiset ℕ},
  legal_op A B → (∀ x, x ∈ B → m ∣ x) → (∀ x, x ∈ A → m ∣ x) :=
induction
(λ a b c X h0,
  suffices m ∣ a + c ∧ m ∣ b + c,
  from λ x h1, (mem_cons.mp h1).elim (λ h1, this.1.trans $ dvd_of_eq h1.symm) $
    λ h1, (mem_cons.mp h1).elim (λ h1, this.2.trans $ dvd_of_eq h1.symm) $
    λ h1, h0 x (mem_cons_of_mem $ mem_cons_of_mem $ mem_cons_of_mem h1),
  suffices m ∣ c,
  from ⟨(h0 a $ mem_cons_self _ _).add this,
    (h0 b $ mem_cons_of_mem $ mem_cons_self _ _).add this⟩,
  odd_dvd_two_mul_imp_dvd h $ h0 _ $ mem_cons_of_mem $
    mem_cons_of_mem $ mem_cons_self _ _)
(λ X h0 x h1, (mem_cons.mp h1).elim
  (λ h1, (dvd_zero m).trans $ dvd_of_eq h1.symm) (h0 x))

end legal_op





/- ### Chain of legal moves: `is_reachable` and its properties -/

def is_reachable := refl_trans_gen legal_op

namespace is_reachable

theorem trans {A B C : multiset ℕ} (h : is_reachable A B) (h0 : is_reachable B C) :
  is_reachable A C :=
  refl_trans_gen.trans h h0

theorem move_pebble (a b c : ℕ) (X : multiset ℕ) :
  is_reachable ((a + c) ::ₘ (b + c) ::ₘ X) (a ::ₘ b ::ₘ (2 * c) ::ₘ X) :=
  refl_trans_gen.single $ legal_op.move_pebble a b c X

theorem remove_zero (X : multiset ℕ) : is_reachable (0 ::ₘ X) X :=
  refl_trans_gen.single $ legal_op.remove_zero X

theorem congr {A B : multiset ℕ} (h : A = B) : is_reachable A B :=
  h ▸ refl_trans_gen.refl

theorem add_right (A : multiset ℕ) {B C : multiset ℕ} (h : is_reachable B C) :
  is_reachable (B + A) (C + A) := 
  refl_trans_gen.head_induction_on h refl_trans_gen.refl $
    λ X Z h h0 h1, h1.head $ legal_op.add_right A h

theorem add_left (A : multiset ℕ) {B C : multiset ℕ} (h : is_reachable B C) :
  is_reachable (A + B) (A + C) := 
  add_comm B A ▸ add_comm C A ▸ add_right A h

theorem add_congr {A B C D : multiset ℕ} (h : is_reachable A B) (h0 : is_reachable C D) :
  is_reachable (A + C) (B + D) :=
  (add_right C h).trans (add_left B h0)

theorem cons_right (a : ℕ) {B C : multiset ℕ} (h : is_reachable B C) :
  is_reachable (a ::ₘ B) (a ::ₘ C) := 
  add_left {a} h

theorem cons_congr {a b : ℕ} (h : a = b) {A B : multiset ℕ} (h0 : is_reachable A B) :
  is_reachable (a ::ₘ A) (b ::ₘ B) :=
  add_congr (congr $ congr_arg singleton h) h0



theorem exists_reachable_no_zero (X : multiset ℕ) :
  ∃ Y : multiset ℕ, is_reachable X Y ∧ (∀ x, x ∈ Y → x ≠ 0) :=
multiset.induction_on X (⟨0, refl_trans_gen.refl, λ x h, absurd h $ not_mem_zero x⟩) $
  λ a X h, exists.elim h $ λ Y h, (eq_or_ne a 0).elim
    (λ h0, ⟨Y, (cons_congr h0 h.1).tail (legal_op.remove_zero Y), h.2⟩)
    (λ h0, ⟨a ::ₘ Y, cons_right a h.1,
      λ x h1, (mem_cons.mp h1).elim (λ h2 h3, h0 $ h2.symm.trans h3) (h.2 x)⟩)

theorem map_mul_left (m : ℕ) {A B : multiset ℕ} (h : is_reachable A B) :
  is_reachable (A.map $ has_mul.mul m) (B.map $ has_mul.mul m) :=
  refl_trans_gen.head_induction_on h refl_trans_gen.refl $
    λ X Z h h0 h1, h1.head $ legal_op.map_mul_left m h

theorem sum_eq {A B : multiset ℕ} (h : is_reachable A B) : A.sum = B.sum :=
  refl_trans_gen.head_induction_on h rfl $ λ X Z h0 h1, (legal_op.sum_eq h0).trans

/-- If `S.sum = 0`, then `0` is reachable from `S` -/
theorem of_sum_eq_zero {S : multiset ℕ} : S.sum = 0 → is_reachable S 0 :=
multiset.induction_on S (λ _, refl_trans_gen.refl) $ λ a S h h0, 
  let h0 := add_eq_zero_iff.mp $ (sum_cons a S).symm.trans h0 in
  (cons_congr h0.1 $ h h0.2).tail $ legal_op.remove_zero 0

lemma sum_ne_zero {A B : multiset ℕ} (h : is_reachable A B) (h0 : A.sum ≠ 0) : B.sum ≠ 0 :=
  λ h1, h0 $ (is_reachable.sum_eq h).trans h1



theorem add_cons_two_cons_to_add_ones (m : ℕ) : ∀ (n : ℕ) (X : multiset ℕ),
  is_reachable ((m + n) ::ₘ 2 ::ₘ X) (m ::ₘ 2 ::ₘ (replicate n 1 + X))
| 0 X := congr $ congr_arg _ $ congr_arg _ $ self_eq_add_left.mpr $ replicate_zero 1
| (n+1) X := refl_trans_gen.head (legal_op.succ_two_to_self_two_one (m + n) X) $
    (add_cons_two_cons_to_add_ones _ _).trans $ cons_right m $ cons_right 2 $
    congr $ (add_cons 1 _ X).trans $ (cons_add 1 _ X).symm

theorem cons_two_cons_to_add_ones (n : ℕ) (X : multiset ℕ) :
  is_reachable (n ::ₘ 2 ::ₘ X) (2 ::ₘ (replicate n 1 + X)) :=
  (cons_congr n.zero_add.symm refl_trans_gen.refl).trans $
    (add_cons_two_cons_to_add_ones 0 n X).tail (legal_op.remove_zero _)

theorem to_cons_two_replicate_one (X : multiset ℕ) :
  is_reachable (2 ::ₘ X) (2 ::ₘ replicate X.sum 1) :=
multiset.induction_on X refl_trans_gen.refl $ λ n X h,
  (congr $ cons_swap 2 n X).trans $ (cons_two_cons_to_add_ones n X).trans $
  by rw [← add_cons, sum_cons, replicate_add, ← add_cons]; exact h.add_left _

theorem cons_cons_to_two_mul_cons (a : ℕ) (X : multiset ℕ) :
  is_reachable (a ::ₘ a ::ₘ X) ((2 * a) ::ₘ X) :=
  let h := a.zero_add.symm in
  (cons_congr h $ cons_congr h refl_trans_gen.refl).trans $
    (move_pebble 0 0 a X).trans $ (remove_zero _).trans $ (remove_zero _)

theorem replicate_two_mul_left_to_right :
  ∀ n a : ℕ, is_reachable (replicate (2 * n) a) (replicate n (2 * a))
| 0 a := refl_trans_gen.refl
| (n+1) a := (cons_cons_to_two_mul_cons a $ replicate (2 * n) a).trans
    (cons_right _ $ replicate_two_mul_left_to_right n a)

theorem replicate_two_pow_mul_left_to_right :
  ∀ n a k : ℕ, is_reachable (replicate (2 ^ k * n) a) (replicate n (2 ^ k * a))
| n a 0 := congr $ congr_arg2 _ n.one_mul a.one_mul.symm
| n a (k+1) := (congr $ congr_arg2 _ (mul_assoc 2 (2 ^ k) n) rfl).trans $
    (replicate_two_mul_left_to_right (2 ^ k * n) a).trans $
    (replicate_two_pow_mul_left_to_right _ _ _).trans $
    congr $ congr_arg2 _ rfl $ (mul_left_comm _ 2 a).trans (mul_assoc 2 _ a).symm

theorem replicate_two_pow_to_singleton (a k : ℕ) :
  is_reachable (replicate (2 ^ k) a) {2 ^ k * a} :=
  (congr $ congr_arg2 _ (nat.mul_one $ 2 ^ k).symm rfl).trans
    (replicate_two_pow_mul_left_to_right 1 a k)

theorem sum_eq_two_pow_to_singleton {k : ℕ} :
  ∀ {X : multiset ℕ}, X.sum = 2 ^ k → is_reachable X {2 ^ k} :=
suffices ∀ {X : multiset ℕ}, (∀ a, a ∈ X → a ≠ 0) → X.sum = 2 ^ k → is_reachable X {2 ^ k},
from λ X h, exists.elim (exists_reachable_no_zero X) $ λ Y h0,
  h0.1.trans $ this h0.2 $ (sum_eq h0.1).symm.trans h,
λ X h h0, (le_or_lt X.card 1).elim
---- Case 1: `|X| ≤ 1`
(λ h1, (nat.le_add_one_iff.mp h1).elim
  (λ h1, absurd h0.symm $ (card_eq_zero.mp $ le_zero_iff.mp h1).symm ▸
    pow_ne_zero k $ nat.succ_ne_zero 1)
  (λ h1, congr $ exists.elim (card_eq_one.mp h1) $ λ a h1,
    h1.trans $ congr_arg singleton $ h0 ▸ h1.symm ▸ rfl))
---- Case 2: `|X| > 1`
(λ h1, exists.elim (legal_op.exists_two_cons_right h h1) $ λ Y h2,
  ((to_cons_two_replicate_one Y).head h2).trans $
begin
  rw [h2.sum_eq, sum_cons] at h0,
  cases k, exact absurd h0.symm (nat.lt_add_right _ _ _ $ nat.lt_succ_self 1).ne,
  obtain ⟨N, h3⟩ : 2 ∣ Y.sum := by rw [← nat.dvd_add_right (dvd_refl 2), h0];
    exact dvd_pow_self 2 k.succ_ne_zero,
  rw [h3, ← mul_one_add, add_comm, pow_succ, mul_eq_mul_left_iff,
      or_iff_left (nat.succ_ne_zero 1)] at h0,
  rw h3; refine (cons_right 2 $ replicate_two_mul_left_to_right N 1).trans _,
  rw [mul_one, ← replicate_succ, h0],
  exact (pow_succ' 2 k).symm ▸ replicate_two_pow_to_singleton 2 k
end)

theorem sum_eq_two_pow_mul_to_singleton_of_dvd_all {k m : ℕ} (h : m ≠ 0) {X : multiset ℕ}
  (h0 : X.sum = 2 ^ k * m) (h1 : ∀ x : ℕ, x ∈ X → m ∣ x) : is_reachable X {2 ^ k * m} :=
begin
  rcases multiset_exists_map_mul_of_dvd_all h1 with ⟨Y, rfl⟩,
  rw [sum_map_mul_left, map_id', mul_comm, mul_eq_mul_right_iff, or_iff_left h] at h0,
  exact m.mul_comm (2 ^ k) ▸ (sum_eq_two_pow_to_singleton h0).map_mul_left m
end



theorem singleton_right_eq {X : multiset ℕ} {N : ℕ} (h : is_reachable X {N}) : N = X.sum :=
  (sum_eq h).symm

theorem card_le_one_right_eq {X Y : multiset ℕ} (h : X.sum ≠ 0)
  (h0 : Y.card ≤ 1) (h1 : is_reachable X Y) : Y = {X.sum} :=
begin
  rw [le_iff_lt_or_eq, nat.lt_one_iff, card_eq_zero, card_eq_one] at h0,
  have h2 := h1.sum_eq,
  refine h0.elim (λ h0, absurd (h2.trans $ congr_arg _ h0) h)
    (λ h0, exists.elim h0 $ λ a h0, h0.trans $ congr_arg singleton _),
  rw [h2, h0, sum_singleton]
end

theorem odd_dvd_all_left_of_right {m : ℕ} (h : odd m) {A B : multiset ℕ}
  (h0 : is_reachable A B) : (∀ x, x ∈ B → m ∣ x) → (∀ x, x ∈ A → m ∣ x) :=
  refl_trans_gen.head_induction_on h0 id $
    λ X Z h1 h2, comp $ legal_op.odd_dvd_all_left_of_right h h1

theorem odd_dvd_sum_imp_of_singleton_right {m : ℕ} (h : odd m) {X : multiset ℕ}
  (h0 : is_reachable X {X.sum}) (h1 : m ∣ X.sum) : ∀ x : ℕ, x ∈ X → m ∣ x :=
  odd_dvd_all_left_of_right h h0 $ λ x h2, h1.trans $ dvd_of_eq (mem_singleton.mp h2).symm



theorem exists_right_card_le_two :
  ∀ X : multiset ℕ, ∃ Y : multiset ℕ, Y.card ≤ 2 ∧ is_reachable X Y :=
---- Reduce to only proving for `X = 2 ::ₘ replicate n 1`
suffices ∀ X : multiset ℕ, (∀ a, a ∈ X → a ≠ 0) →
  ∃ Y : multiset ℕ, Y.card ≤ 2 ∧ is_reachable X Y,
from λ X, exists.elim (exists_reachable_no_zero X) $
  λ X0 h, exists.elim (this X0 h.2) $ λ Y h0, ⟨Y, h0.1, h.1.trans h0.2⟩,
suffices ∀ n : ℕ, ∃ Y : multiset ℕ, Y.card ≤ 2 ∧ is_reachable (2 ::ₘ replicate n 1) Y,
from λ X h, (le_total X.card 2).elim (λ h0, ⟨X, h0, refl_trans_gen.refl⟩) $
  λ h0, exists.elim (legal_op.exists_two_cons_right h h0) $ λ X0 h1, exists.elim (this X0.sum) $
    λ Y h2, ⟨Y, h2.1, ((to_cons_two_replicate_one X0).head h1).trans h2.2⟩,
---- Prove `2 ::ₘ replicate n 1 ⇒ ???`
λ n, begin
  obtain ⟨k, h, h0⟩ : ∃ k : ℕ, 2 ^ k ≤ n + 2  ∧ n + 2 < 2 ^ (k + 1) :=
    ⟨nat.log 2 (n + 2), nat.pow_log_le_self _ (n + 1).succ_ne_zero,
      (n + 2).lt_pow_succ_log_self (nat.lt_succ_self 1)⟩,
  rw [le_iff_eq_or_lt, nat.lt_succ_iff, le_iff_eq_or_lt, nat.lt_succ_iff] at h,
  rcases h with h | h | h,
  -- Case 1: `n = 2^k - 2`
  { refine ⟨{2 ^ k}, nat.le_succ 1, sum_eq_two_pow_to_singleton _⟩,
    rw [sum_cons, sum_replicate, smul_eq_mul, mul_one, add_comm, h] },
  -- Case 2: `n = 2^k - 1`
  { refine ⟨1 ::ₘ {2 ^ k}, le_refl 2, _⟩,
    rw [pow_succ, h, nat.mul_succ, add_lt_add_iff_right, two_mul, lt_add_iff_pos_left] at h0,
    obtain ⟨n0, rfl⟩ := nat.exists_eq_succ_of_ne_zero h0.ne.symm,
    rw [replicate_succ, cons_swap],
    refine cons_right 1 (sum_eq_two_pow_to_singleton _),
    rw [sum_cons, sum_replicate, smul_eq_mul, mul_one, h, add_comm] },
  -- Case 3: `2^k ≤ n < 2^{k + 1} - 2`
  { obtain ⟨m, rfl⟩ := exists_add_of_le h,
    rw [pow_succ, two_mul, add_assoc, add_lt_add_iff_left] at h0,
    refine ⟨(m + 2) ::ₘ {2 ^ k}, le_refl 2, _⟩,
    rw [replicate_add, ← add_cons],
    refine ((replicate_two_pow_to_singleton 1 _).add_right _).trans _,
    obtain ⟨c, h1⟩ := exists_add_of_le h0.le,
    nth_rewrite 0 h1; rw [mul_one, singleton_add],
    refine (add_cons_two_cons_to_add_ones _ _ _).trans
      (cons_right _ $ sum_eq_two_pow_to_singleton _),
    rw [sum_cons, ← replicate_add, sum_replicate, smul_eq_mul,
        mul_one, h1, add_comm, add_assoc, add_comm] }
end

end is_reachable

end IMO2022C6
end IMOSL
