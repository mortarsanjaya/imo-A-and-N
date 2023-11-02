import data.nat.log data.list.perm order.bounds.basic

/-! # IMO 2021 A3 -/

namespace IMOSL
namespace IMO2021A3

open list

/-! ## Extra lemmas -/

lemma succ_le_mul_two_pow_div (a) {b} (h : 0 < b) : a + 1 ≤ 2 ^ (a / b) * b := 
  nat.lt_mul_of_div_lt (a / b).lt_two_pow h

lemma prod_map_succ_iota : ∀ n : ℕ, ((iota n).map nat.succ).prod = (n + 1).factorial
| 0 := rfl
| (n+1) := prod_cons.trans $ congr_arg2 _ rfl (prod_map_succ_iota n)

lemma clog_two_bit0_succ (k : ℕ) : nat.clog 2 (bit0 (k + 1)) = nat.clog 2 (k + 1) + 1 :=
  (bit0_eq_two_mul (k + 1)).symm ▸
    (nat.clog_of_two_le (nat.lt_succ_self 1) (nat.le_mul_of_pos_right k.succ_pos)).trans
    (suffices (2 * k.succ + 1) / 2 = k.succ, from congr_arg nat.succ $ congr_arg _ this,
    nat.add_comm 1 (2 * k.succ) ▸ (nat.add_mul_div_left _ _ (nat.succ_pos 1)).trans (zero_add _))

lemma clog_two_bit1_succ (k : ℕ) : nat.clog 2 (bit1 (k + 1)) = nat.clog 2 (k + 1 + 1) + 1 :=
  (nat.bit1_eq_succ_bit0 (k + 1)).symm ▸ (bit0_eq_two_mul (k + 1)).symm ▸
    (nat.clog_of_two_le (nat.lt_succ_self 1)
      (nat.le_succ_of_le $ nat.le_mul_of_pos_right k.succ_pos)).trans
    (congr_arg nat.succ $ congr_arg _ $ nat.mul_div_cancel_left (k + 1 + 1) (nat.succ_pos 1))





/-! ## Start of the problem -/

def target_sum : list ℕ → ℕ
| [] := 0
| (a :: l) := a / l.length.succ + target_sum l



lemma target_sum_general_lower_bound :
  ∀ l : list ℕ, (l.map nat.succ).prod ≤ 2 ^ target_sum l * l.length.factorial
| [] := nat.le_refl 1
| (a :: l) := prod_cons.trans_le $
    (nat.mul_le_mul (succ_le_mul_two_pow_div a l.length.succ_pos)
      (target_sum_general_lower_bound l)).trans_eq $
    (mul_mul_mul_comm _ _ _ _).trans $ congr_arg2 _ (pow_add _ _ _).symm rfl

lemma target_sum_perm_iota_n_lower_bound {n : ℕ} {l : list ℕ} (h : l ~ iota n) :
  nat.clog 2 (n + 1) ≤ target_sum l :=
(nat.le_pow_iff_clog_le $ nat.lt_succ_self 1).mp $
  le_of_mul_le_mul_right ((target_sum_general_lower_bound l).trans_eq' $
    h.length_eq.symm ▸ (length_iota n).symm ▸ (h.map nat.succ).prod_eq.symm ▸
    (prod_map_succ_iota n).symm) l.length.factorial_pos



/-- Given a list `l : list ℕ` of length `k` and `n : ℕ`, return
  `[k + n - 1, ..., k] ++ l` -/
def iota_append (l : list ℕ) : ℕ → list ℕ
| 0 := l
| (n+1) := (l.length + n) :: iota_append n

lemma perm_iota_append_of_perm {l₁ l₂ : list ℕ} (h : l₁ ~ l₂) :
  ∀ n : ℕ, iota_append l₁ n ~ iota_append l₂ n
| 0 := h
| (n+1) := ((perm_iota_append_of_perm n).cons _).trans $ h.length_eq.symm ▸ perm.refl _

lemma perm_iota_append_cons_iota (k a : ℕ) :
  ∀ n : ℕ, iota_append (a :: iota k) n ~ a :: iota (k + n)
| 0 := perm.refl _
| (n+1) := ((perm_iota_append_cons_iota n).cons _).trans $ (perm.swap _ _ _).trans $
    perm.cons _ $ ((iota k).length_cons a).symm ▸ (length_iota k).symm ▸
    k.add_assoc n 1 ▸ k.add_right_comm n 1 ▸ perm.refl _

lemma perm_iota_append_of_perm_cons_iota
  {k a : ℕ} {l : list ℕ} (h : l ~ a :: iota k) (n : ℕ) :
  iota_append l n ~ a :: iota (k + n) :=
(perm_iota_append_of_perm h n).trans (perm_iota_append_cons_iota k a n)

lemma perm_iota_append_iota {k n : ℕ} {l : list ℕ} (h : l ~ (k + n + 1) :: iota k) :
  iota_append l n ~ iota (k + n + 1) :=
  perm_iota_append_of_perm_cons_iota h n

lemma length_iota_append (l : list ℕ) : ∀ n, (iota_append l n).length = l.length + n
| 0 := rfl
| (n+1) := congr_arg nat.succ (length_iota_append n)

lemma target_sum_iota_append (l : list ℕ) :
  ∀ n : ℕ, target_sum (iota_append l n) = target_sum l
| 0 := rfl
| (n+1) := let h : (l.length + n) / (iota_append l n).length.succ = 0 :=
      nat.div_eq_of_lt $ (length_iota_append l n).symm ▸ nat.lt_succ_self _ in
    (congr_arg2 has_add.add h rfl).trans $ (nat.zero_add _).trans (target_sum_iota_append n)



/-- The main construction -/
def lower_bound_mk : ℕ → list ℕ :=
nat.binary_rec [] $ λ b n l,
  match b, n with
  | ff, 0 := l
  | ff, k+1 := iota_append (bit0 (k+1) :: l) k
  | tt, n := iota_append (bit1 n :: l) n
  end

lemma lower_bound_mk_zero : lower_bound_mk 0 = [] :=
  nat.binary_rec_zero _ _

lemma lower_bound_mk_bit0_succ (k : ℕ) :
  lower_bound_mk (bit0 (k + 1)) = iota_append (bit0 (k + 1) :: lower_bound_mk (k + 1)) k :=
  nat.binary_rec_eq (by refl) ff (k + 1)

lemma lower_bound_mk_bit1 (n : ℕ) :
  lower_bound_mk (bit1 n) = iota_append (bit1 n :: lower_bound_mk n) n :=
  nat.binary_rec_eq (by refl) tt n

lemma lower_bound_mk_perm_iota : ∀ n, lower_bound_mk n ~ iota n :=
let X := perm_nil.mpr lower_bound_mk_zero in
nat.binary_rec X $ λ b n, match b, n with
| ff, 0 := λ _, X
| ff, k+1 := λ h, (lower_bound_mk_bit0_succ k).symm ▸ perm_iota_append_iota (h.cons _)
| tt, n := λ h, (lower_bound_mk_bit1 n).symm ▸ perm_iota_append_iota (h.cons _)
end

lemma lower_bound_mk_length (n : ℕ) : (lower_bound_mk n).length = n :=
  (lower_bound_mk_perm_iota n).length_eq.trans (length_iota n)

lemma lower_bound_mk_target_sum_bit0_succ (k : ℕ) :
  target_sum (lower_bound_mk (bit0 (k + 1))) = target_sum (lower_bound_mk (k + 1)) + 1 :=
(lower_bound_mk_bit0_succ k).symm ▸ (target_sum_iota_append _ _).trans
  ((add_comm _ _).trans $ congr_arg2 _ rfl $ (lower_bound_mk_length (k + 1)).symm ▸
    nat.div_eq_of_lt_le
      ((nat.one_mul _).trans_le $ nat.succ_le_succ $ nat.le_add_right _ _)
      ((bit0_eq_two_mul _).trans_lt $
        nat.mul_lt_mul_of_pos_left (k + 1).lt_succ_self (nat.succ_pos 1)))

lemma lower_bound_mk_target_sum_bit1 (n : ℕ) :
  target_sum (lower_bound_mk (bit1 n)) = target_sum (lower_bound_mk n) + 1 :=
(lower_bound_mk_bit1 n).symm ▸ (target_sum_iota_append _ _).trans
  ((add_comm _ _).trans $ congr_arg2 _ rfl $ (lower_bound_mk_length n).symm ▸
    nat.div_eq_of_lt_le
      (nat.succ_le_succ $ n.one_mul.trans_le $ n.le_add_right n)
      ((bit1 n).lt_succ_self.trans_eq $
        congr_arg nat.succ $ congr_arg nat.succ $ bit0_eq_two_mul n))

lemma lower_bound_mk_target_sum : ∀ n, target_sum (lower_bound_mk n) = nat.clog 2 (n + 1) :=
let X : target_sum (lower_bound_mk 0) = nat.clog 2 1 :=
    (congr_arg target_sum lower_bound_mk_zero).trans (nat.clog_one_right 2).symm,
  Y : 1 < 2 := nat.lt_succ_self 1 in
nat.binary_rec X $ λ b n, match b, n with
| ff, 0 := λ _, X
| ff, k+1 := λ h, (lower_bound_mk_target_sum_bit0_succ k).trans $
    h.symm ▸ (clog_two_bit1_succ k).symm
| tt, n := λ h, (lower_bound_mk_target_sum_bit1 n).trans $
    h.symm ▸ (clog_two_bit0_succ n).symm.trans (congr_arg _ $ add_add_add_comm n 1 n 1)
end





/-- Final solution -/
theorem final_solution {n : ℕ} :
  is_least (target_sum '' {l : list ℕ | l ~ iota n}) (nat.clog 2 (n + 1)) :=
⟨⟨lower_bound_mk n, lower_bound_mk_perm_iota n, lower_bound_mk_target_sum n⟩,
λ N h, exists.elim h $ λ l h, (target_sum_perm_iota_n_lower_bound h.1).trans_eq h.2⟩

end IMO2021A3
end IMOSL
