import ring_theory.coprime.lemmas ring_theory.ideal.basic

/-! # IMO 2012 N1 -/

namespace IMOSL
namespace IMO2012N1

def admissible {R : Type*} [semiring R] (A : set R) :=
  ∀ x y : R, x ∈ A → y ∈ A → ∀ r : R, x ^ 2 + r * x * y + y ^ 2 ∈ A



private lemma admissible_ideal {R : Type*} [comm_semiring R] (I : ideal R) :
  admissible (I : set R) :=
  λ u v h h0 r, by rw [sq, mul_right_comm, ← add_mul, sq];
    exact I.add_mem (I.mul_mem_left (u + r * v) h) (I.mul_mem_left v h0)

private lemma admissible_mem_sq_mul {R : Type*} [comm_ring R]
  {A : set R} (h : admissible A) {z : R} (h0 : z ∈ A) (k : R) :
  k * z ^ 2 ∈ A :=
  by replace h := h z z h0 h0 (k - (1 + 1));
    rwa [mul_assoc, ← sq, ← one_add_mul, ← add_one_mul,
      add_right_comm, add_sub_cancel'_right] at h





/-- Final solution -/
theorem final_solution {R : Type*} [comm_ring R] (x y : R) :
  (∀ A : set R, admissible A → x ∈ A → y ∈ A → ∀ z : R, z ∈ A) ↔ is_coprime x y :=
begin
  refine ⟨λ h, _, λ h A h0 h1 h2, _⟩,

  ---- If the only admissible set containing `x` and `y` is `R`, then `x` and `y` are coprime.
  { replace h := h _ (admissible_ideal $ ideal.span {x, y})
      (ideal.subset_span $ set.mem_insert x _)
      (ideal.subset_span $ set.mem_insert_of_mem _ $ set.mem_singleton y) 1,
    rw [set_like.mem_coe, ideal.mem_span_insert] at h,
    rcases h with ⟨a, z, h0, h⟩,
    rw ideal.mem_span_singleton at h0; rcases h0 with ⟨b, rfl⟩,
    rw mul_comm y at h; exact ⟨a, b, h.symm⟩ },

  ---- If `x` and `y` are coprime, the only admissible set `x` and `y` is `R`
  suffices : (1 : R) ∈ A,
  { intros x,
    rw [← mul_one x, ← one_pow 2],
    exact admissible_mem_sq_mul h0 this x },
  { replace h : is_coprime (x ^ 2) (y ^ 2) := is_coprime.pow h,
    rcases h with ⟨a, b, h⟩,
    replace h0 := h0 _ _ (admissible_mem_sq_mul h0 h1 a) (admissible_mem_sq_mul h0 h2 b) 2,
    rwa [← add_sq, h, one_pow] at h0 }
end 

end IMO2012N1
end IMOSL
