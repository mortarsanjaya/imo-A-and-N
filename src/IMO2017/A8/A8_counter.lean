import IMO2017.A8.A8_general data.int.basic tactic.linarith

/-! # IMO 2017 A8, counter-example for G = ℤ -/

namespace IMOSL
namespace IMO2017A8

/-- The counter-example. Note that obviously, 0 < 1 and f(0) > f(1). -/
def counter (x : ℤ) := ite (x = 0) 2 (ite (x = 1) 0 (2 * x))

private lemma counter_eq0 : counter 0 = 2 :=
  by simp only [counter, if_true, eq_self_iff_true]

private lemma counter_eq1 : counter 1 = 0 :=
  by simp only [counter, if_true, eq_self_iff_true, one_ne_zero, if_false]

private lemma counter_ne01 {x : ℤ} (h : x ∉ ({0, 1} : finset ℤ)) : counter x = 2 * x :=
begin
  rw [finset.mem_insert, finset.mem_singleton, not_or_distrib] at h,
  cases h with h h0,
  simp only [counter, h, h0, if_false]
end



/-- The counter-example is indeed a good function. -/
theorem counter_good : good counter :=
begin
  intros x y h,
  by_cases h0 : x ∈ ({0, 1} : finset ℤ),
  rw [finset.mem_insert, finset.mem_singleton] at h0,
  work_on_goal 2 { rw [counter_ne01 h0] at h ⊢ },
  rcases h0 with rfl | rfl,
  all_goals {
    by_cases h1 : y ∈ ({0, 1} : finset ℤ),
    rw [finset.mem_insert, finset.mem_singleton] at h1,
    work_on_goal 2 { rw [counter_ne01 h1] at h ⊢ },
    rcases h1 with rfl | rfl },
  all_goals {
    simp only [counter_eq0, counter_eq1] at h ⊢,
    split; linarith }
end

end IMO2017A8
end IMOSL
