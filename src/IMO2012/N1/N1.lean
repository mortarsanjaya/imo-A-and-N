import ring_theory.coprime.lemmas ring_theory.ideal.basic

/-! # IMO 2012 N1 -/

namespace IMOSL
namespace IMO2012N1

def admissible {R : Type*} [semiring R] (A : set R) := ∀ x y : R, x ∈ A → y ∈ A → ∀ r : R, x ^ 2 + r * x * y + y ^ 2 ∈ A



/-- Final solution -/
theorem final_solution {R : Type*} [comm_ring R] (x y : R) :
  (∀ A : set R, admissible A → x ∈ A → y ∈ A → ∀ z : R, z ∈ A) ↔ is_coprime x y :=
begin
  refine ⟨λ h, _, λ h A h0 h1 h2, _⟩,

  ---- If the only admissible set containing `x` and `y` is `R`, then `x` and `y` are coprime.
  { have h0 : ∀ I : ideal R, admissible (I : set R) :=
      λ I u v h h0 r, by rw [sq, mul_right_comm, ← add_mul, sq];
        exact I.add_mem (I.mul_mem_left _ h) (I.mul_mem_left _ h0),
    replace h := h _ (h0 (ideal.span {x, y})) (ideal.subset_span (set.mem_insert x _))
      (ideal.subset_span (set.mem_insert_of_mem _ (set.mem_singleton y))) 1,
    simp_rw [set_like.mem_coe, ideal.mem_span_insert, ideal.mem_span_singleton] at h,
    rcases h with ⟨a, z, ⟨b, rfl⟩, h⟩,
    rw mul_comm y at h; exact ⟨a, b, h.symm⟩ },

  ---- If `x` and `y` are coprime, the only admissible set `x` and `y` is `R`
  { have h3 : ∀ z : R, z ∈ A → (∀ k : R, k * z ^ 2 ∈ A) :=
      λ x h3 k, by replace h3 := h0 x x h3 h3 (k - (1 + 1));
        rwa [mul_assoc, ← sq, ← one_add_mul, add_comm (1 : R),
             ← add_one_mul, add_assoc, sub_add_cancel] at h3,
    suffices : (1 : R) ∈ A,
      intros x; convert h3 1 this x; rw [one_pow, mul_one],
    replace h : is_coprime (x ^ 2) (y ^ 2) := is_coprime.pow h,
    rcases h with ⟨a, b, h⟩,
    replace h1 := h3 x h1 a,
    replace h2 := h3 y h2 b,
    replace h0 := h0 _ _ h1 h2 2,
    rwa [← add_sq, h, one_pow] at h0 }
end 

end IMO2012N1
end IMOSL
