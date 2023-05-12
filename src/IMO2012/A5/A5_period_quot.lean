import IMO2012.A5.A5_basic ring_theory.ideal.quotient

/-!
# IMO 2012 A5, Quotient by Ideal of Periods

Let `R` be a commutative ring and `f : R → S` be a good function.
We prove that `f(c + x) = -f(c) f(x) ↔ f(cx + 1) = 0` for any `c, x : R`.
Let `J ⊆ R` be the set of `c : R` satisfying the two equalities for all `x : R`.
We show that `J` is an ideal.
If `S` is a domain and `f ≠ 0`, we also get `f(c) ∈ {-1, 1}` for all `c ∈ J`.

Let `I ⊆ R` be the set of `c : R` satisfying `f(c + x) = f(x)` for all `x : R`.
We show that `I` is also an ideal, and in fact `I ⊆ J`. 
As an implication, `f` factors through as `g ∘ φ`, where `φ : R → R/I` is
  the canonical map and `g : R/I → S` is the induced (good) map.
-/

namespace IMOSL
namespace IMO2012A5

variables {R S : Type*}

section noncomm_ring

variables [ring R] [ring S]

lemma quasi_period_iff {f : R → S} (h : good f) {c : R} :
  (∀ x, f (c + x) = -f c * f x) ↔ (∀ x, f (c * x + 1) = 0) :=  
  forall_congr $ λ x, by rw [neg_mul, ← h, neg_sub, eq_comm]; exact sub_eq_self

lemma quasi_period_add {f : R → S} (h : good f) {c d : R} (h0 : ∀ x, f (c * x + 1) = 0)
 (h1 : ∀ x, f (d * x + 1) = 0) : ∀ x, f ((c + d) * x + 1) = 0 :=
  by rw ← quasi_period_iff h at h0 h1 ⊢; intros x;
    rw [h0, add_assoc, h0, h1, ← mul_assoc, ← mul_neg]

variables [is_domain S] {f : R → S} (h : good f)
include h

private lemma neg_map_zero_mul (x : R) : -f 0 * f x = f x :=
  by rw [neg_mul, ← h, zero_mul, zero_add, zero_add, good_map_one h, zero_sub, neg_neg]

lemma period_iff {f : R → S} (h : good f) {c : R} :
  (∀ x, f (c + x) = f x) ↔ ((∀ x, f (c + x) = -f c * f x) ∧ f c = f 0) :=
  ⟨λ h0, (and_iff_right_of_imp $ by intros h1 x; rw [h0, h1, neg_map_zero_mul h]).mpr $
    (congr_arg f (add_zero c).symm).trans $ h0 0,
  λ h0 x, (h0.1 x).trans $ (congr_arg (λ t, -t * f x) h0.2).trans $ neg_map_zero_mul h x⟩

lemma period_imp_quasi_period {f : R → S} (h : good f)
  {c : R} (h0 : ∀ x, f (c + x) = f x) : ∀ x, f (c * x + 1) = 0 :=
  λ x, sub_eq_neg_self.mp $ (h c x).trans $
    by rw [h0, ← add_zero c, h0, ← h, zero_add, sub_eq_neg_self, zero_mul, zero_add];
      exact good_map_one h

variables (h0 : f 0 = -1)
include h0

lemma map_quasi_period {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) :
  f c = 1 ∨ f c = -1 :=
begin
  have h2 := h (c + 1) (-1),
  rw [h1, good_map_one h, mul_zero, zero_mul, sub_eq_zero, add_one_mul,
      neg_add_cancel_right, add_neg_cancel_right, mul_neg_one] at h2,
  replace h1 := h1 (-c),
  rwa [add_neg_self, h0, h2, neg_mul, neg_inj] at h1,
  exact mul_self_eq_one_iff.mp h1.symm
end

lemma map_quasi_period_ne_zero {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) : f c ≠ 0 :=
  (map_quasi_period h h0 h1).elim (λ h2 h3, one_ne_zero $ h2.symm.trans h3)
    (λ h2 h3, neg_ne_zero.mpr one_ne_zero $ h2.symm.trans h3)

end noncomm_ring



section comm_ring

variables [comm_ring R] [ring S] [is_domain S] {f : R → S} (h : good f)
include h 

def quasi_period_ideal : ideal R :=
{ carrier := {c | ∀ x, f (c * x + 1) = 0},
  add_mem' := λ a b, quasi_period_add h,
  zero_mem' := λ x, (congr_arg f $ add_left_eq_self.mpr $ zero_mul x).trans (good_map_one h),
  smul_mem' := λ a b h1 x, (congr_arg (λ x, f (x + 1)) $
    by rw [smul_eq_mul, mul_comm a b, mul_assoc]).trans (h1 $ a * x) }

def mem_quasi_period_ideal_iff {c : R} :
  c ∈ quasi_period_ideal h ↔ ∀ x, f (c + x) = -f c * f x :=
  (quasi_period_iff h).symm

lemma period_mul {c : R} (h0 : ∀ x, f (c + x) = f x) : ∀ d x, f (d * c + x) = f x :=
begin
  refine (em $ f 0 = -1).elim (λ h1, _)
    (λ h1 d x, by rw eq_zero_of_map_zero_ne_neg_one h h1; refl),

  suffices h2 : ∀ d, (∃ x, f (d * x + 1) ≠ 0) → ∀ x, f (d * c + x) = f x,
  { intros d,
    refine (em $ ∀ x, f (d * x + 1) = 0).elim (λ h3 x, _) (λ h3, h2 d $ not_forall.mp h3),
    rw [← sub_add_add_cancel _ _ c, add_comm x c, ← sub_one_mul],
    refine (h2 _ ⟨1, _⟩ _).trans (h0 x),
    rw [mul_one, sub_add_cancel],
    exact map_quasi_period_ne_zero h h1 ((quasi_period_iff h).mpr h3) },

  rintros d ⟨x, h2⟩,
  have h3 := h (c + x) d,
  rw [h0, add_assoc, h0, ← h, sub_left_inj, add_mul, add_assoc] at h3,
  rw [period_iff h, quasi_period_iff h] at h0 ⊢,
  refine ⟨λ x, _, _⟩,
  rw [mul_comm d c, mul_assoc]; exact h0.1 (d * x),
  have h5 : c * d ∈ quasi_period_ideal h := ideal.mul_mem_right d _ h0.1,
  rw mem_quasi_period_ideal_iff h at h5,
  rwa [h5, mul_left_eq_self₀, mul_comm x d, or_iff_left h2,
       neg_eq_iff_eq_neg, mul_comm, ← h1] at h3,
end

def period_ideal : ideal R :=
{ carrier := {c | ∀ x, f (c + x) = f x},
  add_mem' := λ a b h1 h2 x, (congr_arg f $ add_assoc a b x).trans $
                (h1 $ b + x).trans (h2 x),
  zero_mem' := λ x, congr_arg f $ zero_add x,
  smul_mem' := λ d c h0, period_mul h h0 d }

lemma period_ideal_le_quasi_period_ideal : period_ideal h ≤ quasi_period_ideal h :=
  λ _, period_imp_quasi_period h

lemma period_equiv_imp_f_eq {a b : R}
  (h0 : ideal.quotient.ring_con (period_ideal h) a b) : f a = f b :=
  (congr_arg f (sub_add_cancel a b).symm).trans $
    ideal.quotient.eq.mp ((ring_con.eq _).mpr h0) b

/-- Lifting of `f` along the ideal of periods. -/
def period_lift : R ⧸ period_ideal h → S :=
  quot.lift f $ λ a b, period_equiv_imp_f_eq h

lemma period_lift_is_good : good (period_lift h) :=
  good_of_comp_hom_good_surjective ideal.quotient.mk_surjective h

lemma period_lift_comp_quotient_eq_f :
  period_lift h ∘ ideal.quotient.mk (period_ideal h) = f := rfl

lemma zero_of_periodic_period_lift : ∀ c : R ⧸ period_ideal h,
  (∀ x, period_lift h (c + x) = period_lift h x) → c = 0 :=
  quot.ind $ by intros c h0;
    exact ideal.quotient.eq_zero_iff_mem.mpr (λ y, h0 $ quot.mk _ y)

end comm_ring

end IMO2012A5
end IMOSL
