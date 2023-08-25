import logic.relation data.nat.interval data.nat.factorization.basic combinatorics.colex

/-! # IMO 2009 C1 -/

namespace IMOSL
namespace IMO2009C1

open relation finset

/- ### Extra lemmas -/

lemma and_and_or_not_iff (P Q R : Prop) : (P ∧ Q) ∧ (R ∨ ¬Q) ↔ (P ∧ R) ∧ Q :=
  by rw [and_assoc, and_or_distrib_left, and_not_self, or_false, and_assoc, and_comm Q]

lemma Iic_filter_dvd_card (k n : ℕ) :
  ((Icc k (k + n)).filter $ λ i : ℕ, n + 1 ∣ i + 1).card = 1 :=
  let h := (k + (n + 1)).card_multiples (n + 1) in
  by rwa [range_eq_Ico, ← Ico_union_Ico_eq_Ico k.zero_le le_self_add, filter_union,
    card_union_eq (disjoint_filter_filter $ Ico_disjoint_Ico_consecutive 0 k _),
    ← range_eq_Ico, nat.card_multiples, k.add_div_right n.succ_pos,
    nat.succ_eq_add_one, add_right_inj, ← add_assoc, nat.Ico_succ_right] at h

section symm_diff

variables {α : Type*} [decidable_eq α] (A B : finset α)

lemma disjoint_symm_diff_inter : disjoint (A ∆ B) (A ∩ B) :=
  disjoint_symm_diff_inf A B

lemma symm_diff_union_inter_eq_union : (A ∆ B) ∪ (A ∩ B) = A ∪ B :=
  symm_diff_sup_inf A B

lemma symm_diff_card_add_two_mul_inter_card :
  (A ∆ B).card + 2 * (A ∩ B).card = A.card + B.card :=
  by rw [two_mul, ← add_assoc, ← card_union_eq (disjoint_symm_diff_inter A B),
    symm_diff_union_inter_eq_union, card_union_add_card_inter]

lemma symm_diff_card_mod_two : (A ∆ B).card % 2 = (A.card + B.card) % 2 :=
  by rw [← symm_diff_card_add_two_mul_inter_card, nat.add_mul_mod_self_left]

lemma mem_symm_diff_iff_mem_left {B : finset α} {a : α} (h : a ∉ B) :
  a ∈ A ∆ B ↔ a ∈ A :=
  mem_union.trans $ (or_iff_left $ not_mem_sdiff_of_not_mem_left h).trans $
    mem_sdiff.trans $ and_iff_left h

lemma filter_symm_diff (p : α → Prop) [decidable_pred p] :
  (A ∆ B).filter p = A.filter p ∆ B.filter p :=
  finset.ext $ λ x, by rw [mem_filter, mem_symm_diff, mem_symm_diff,
    mem_filter, mem_filter, not_and_distrib, not_and_distrib,
    and_and_or_not_iff, and_and_or_not_iff, ← or_and_distrib_right]

end symm_diff




/- ### Setup -/

structure GameState (n : ℕ) :=
(board : finset ℕ)
(num_moves : ℕ)

namespace GameState

def init (M n : ℕ) : GameState n :=
{ board := range M,
  num_moves := 0 }

inductive valid_move {n : ℕ} (X : GameState n) : GameState n → Prop
| flip (i : ℕ) (h : i + n ∈ X.board) :
    valid_move ⟨X.board ∆ Icc i (i + n), X.num_moves.succ⟩

def is_reachable {n : ℕ} : GameState n → GameState n → Prop :=
  refl_trans_gen valid_move

def ends {n : ℕ} (X : GameState n) :=
  ∀ Y : GameState n, ¬X.valid_move Y



lemma valid_move_board {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  ∃ i : ℕ, i + n ∈ X.board ∧ Y.board = X.board ∆ Icc i (i + n) :=
  valid_move.cases_on h $ λ i h0, ⟨i, h0, rfl⟩

lemma valid_move_num_moves {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  Y.num_moves = X.num_moves + 1 :=
  valid_move.cases_on h $ λ _ _, rfl

lemma num_moves_init (M n : ℕ) : (init M n).num_moves = 0 := rfl

lemma ends_iff {n : ℕ} {X : GameState n} : X.ends ↔ X.board ⊆ range n :=
⟨λ h i h0, mem_range.mpr $ lt_of_not_le $ λ h1, suffices i - n + n ∈ X.board,
  from h _ $ valid_move.flip (i - n) this, (nat.sub_add_cancel h1).symm ▸ h0,
λ h Y h0, valid_move.cases_on h0 $ λ i h1, (mem_range.mp $ h h1).not_le le_add_self⟩





/- ### Game termination -/

lemma valid_move_colex {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  Y.board.to_colex < X.board.to_colex :=
  valid_move.cases_on h $ λ i h0, (colex.lt_def _ _).mpr $
  ⟨i + n,
    λ j h1, mem_symm_diff_iff_mem_left _ $ λ h2, h1.not_le (mem_Icc.mp h2).2,
    disjoint_right.mp (disjoint_symm_diff_inter _ _) $
      mem_inter.mpr ⟨h0, right_mem_Icc.mpr le_self_add⟩,
    h0⟩

lemma valid_move_sum_two_pow {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  Y.board.sum (pow (2 : ℕ)) < X.board.sum (pow (2 : ℕ)) :=
  (colex.sum_two_pow_lt_iff_lt Y.board X.board).mpr $ valid_move_colex h

lemma valid_move_sum_two_pow_add_num_moves
  {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  Y.board.sum (pow (2 : ℕ)) + Y.num_moves ≤ X.board.sum (pow (2 : ℕ)) + X.num_moves :=
  nat.le_of_lt_succ $ add_lt_add_of_lt_of_le
    (valid_move_sum_two_pow h) (valid_move_num_moves h).le

lemma is_reachable_sum_two_pow_add_num_moves
  {n : ℕ} {X Y : GameState n} (h : X.is_reachable Y) :
  Y.board.sum (pow (2 : ℕ)) + Y.num_moves ≤ X.board.sum (pow (2 : ℕ)) + X.num_moves :=
  refl_trans_gen.head_induction_on h (le_refl _) $
    λ X Z h0 h1 h2, h2.trans $ valid_move_sum_two_pow_add_num_moves h0

/-- The number of moves made is always at most `2 ^ M - 1`. -/
theorem moves_lt_two_pow {M n : ℕ} (X : GameState n) (h : (init M n).is_reachable X) :
  X.num_moves < 2 ^ M :=
  le_add_self.trans_lt $ (is_reachable_sum_two_pow_add_num_moves h).trans_lt $
    (nat.add_zero _).trans_lt $ nat.sum_two_pow_lt $ λ i, mem_range.mp





/- ### Winner of the game -/

/-- The set of central cards with `1` face-up -/
def central_cards {n : ℕ} (X : GameState n) : finset ℕ :=
  X.board.filter (λ i : ℕ, n + 1 ∣ i + 1)

lemma valid_move_central_card_mod_two {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  Y.central_cards.card % 2 = (X.central_cards.card + 1) % 2 :=
  valid_move.cases_on h $ λ i _, by rw [central_cards, filter_symm_diff,
    ← central_cards, symm_diff_card_mod_two, Iic_filter_dvd_card]

lemma valid_move_central_card_add_num_moves_mod_two
  {n : ℕ} {X Y : GameState n} (h : X.valid_move Y) :
  (Y.central_cards.card + Y.num_moves) % 2 = (X.central_cards.card + X.num_moves) % 2 :=
  by rw [valid_move_num_moves h, nat.add_mod, valid_move_central_card_mod_two h,
    ← nat.add_mod, add_add_add_comm, ← bit0, nat.add_mod_right]

lemma is_reachable_central_card_add_num_moves_mod_two
  {n : ℕ} {X Y : GameState n} (h : X.is_reachable Y) :
  (Y.central_cards.card + Y.num_moves) % 2 = (X.central_cards.card + X.num_moves) % 2 :=
  refl_trans_gen.head_induction_on h rfl $
    λ X Z h0 h1 h2, h2.trans $ valid_move_central_card_add_num_moves_mod_two h0

lemma filter_central_init_card (M n : ℕ) :
  (init M n).central_cards.card = M / n.succ :=
  M.card_multiples n.succ

lemma filter_central_ends {n : ℕ} {X : GameState n} (h : X.ends) :
  X.central_cards = ∅ :=
  (filter_eq_empty_iff _).mpr $ λ i h0, nat.not_dvd_of_pos_of_lt i.succ_pos $
    nat.succ_lt_succ $ mem_range.mp $ ends_iff.mp h h0

/-- The number of moves made has the same parity as `⌊M/n⌋` when the game ends. -/
theorem moves_mod_two_eq_div_of_ends {M n : ℕ}
  (X : GameState n) (h : (init M n).is_reachable X) (h0 : X.ends) :
  X.num_moves % 2 = (M / n.succ) % 2 :=
  let h1 := is_reachable_central_card_add_num_moves_mod_two h in
    by rwa [filter_central_init_card, num_moves_init, nat.add_zero,
      filter_central_ends h0, card_empty, nat.zero_add] at h1

end GameState





/- ### Final solution -/

/-- Final solution: Game termination -/
alias GameState.moves_lt_two_pow ← final_solution_max_moves

/-- Final solution: Determining the winner -/
alias GameState.moves_mod_two_eq_div_of_ends ← final_solution_winner

end IMO2009C1
end IMOSL
