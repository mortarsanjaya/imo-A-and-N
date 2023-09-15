import ring_theory.coprime.lemmas ring_theory.ideal.basic

/-! # IMO 2012 N1 -/

namespace IMOSL
namespace IMO2012N1

def admissible {R : Type*} [semiring R] (A : set R) :=
  ∀ x y : R, x ∈ A → y ∈ A → ∀ r : R, x ^ 2 + r * x * y + y ^ 2 ∈ A



lemma admissible_ideal {R : Type*} [comm_semiring R] (I : ideal R) :
  admissible (I : set R) :=
  λ u v h h0 r, (sq u).symm ▸ (sq v).symm ▸ I.add_mem
    (I.add_mem (I.mul_mem_left u h) (I.mul_mem_left (r * u) h0)) (I.mul_mem_left v h0)

lemma admissible_mem_sq_mul {R : Type*} [comm_ring R] {A : set R} (h : admissible A)
  {z : R} (h0 : z ∈ A) (k : R) : k * z ^ 2 ∈ A :=
suffices z ^ 2 + (k - 2) * z * z + z ^ 2 = k * z ^ 2, from this ▸ h z z h0 h0 _,
(mul_assoc (k - 2) z z).symm ▸ sq z ▸ add_right_comm (z ^ 2) (z ^ 2) ((k - 2) * z ^ 2) ▸
  two_mul (z ^ 2) ▸ add_mul 2 (k - 2) (z ^ 2) ▸
  congr_arg2 has_mul.mul (add_sub_cancel'_right 2 k) rfl

lemma admissible_add_sq {R : Type*} [comm_semiring R] {A : set R} (h : admissible A)
  {x y : R} (h0 : x ∈ A) (h1 : y ∈ A) : (x + y) ^ 2 ∈ A :=
  (add_sq x y).symm ▸ h x y h0 h1 2





/-- Final solution -/
theorem final_solution {R : Type*} [comm_ring R] (x y : R) :
  (∀ A : set R, admissible A → x ∈ A → y ∈ A → ∀ z : R, z ∈ A) ↔ is_coprime x y :=
---- `→`
⟨λ h, exists.elim (ideal.mem_span_insert.mp $ h _
    (admissible_ideal $ ideal.span {x, y}) (ideal.subset_span $ set.mem_insert x _)
    (ideal.subset_span $ set.mem_insert_of_mem _ $ set.mem_singleton y) 1) $
λ a h, exists.elim h $ λ z h, exists.elim h $ λ h0 h,
  exists.elim (ideal.mem_span_singleton.mp h0) $ λ b h0,
⟨a, b, mul_comm y b ▸ h0 ▸ h.symm⟩,
---- `←`
λ h A h0 h1 h2, suffices (1 : R) ∈ A,
  from λ x, mul_one x ▸ (one_pow 2 : (1 : R) ^ 2 = 1) ▸ admissible_mem_sq_mul h0 this x,
exists.elim (h.pow : is_coprime (x ^ 2) (y ^ 2)) $ λ a h, exists.elim h $ λ b h,
  let h0 := admissible_add_sq h0 (admissible_mem_sq_mul h0 h1 a)
    (admissible_mem_sq_mul h0 h2 b) in by rwa [h, one_pow] at h0⟩

end IMO2012N1
end IMOSL
