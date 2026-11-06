module

public import PaperP1.Algebra.P3HomogeneousCoefficientFamily
public import PaperP1.Algebra.FiniteRowKernel
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # An actual coefficient-controlled homogeneous integer equation for every finite rational surface population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3HomogeneousIntegerInterpolation

open MvPolynomial Finset Matrix P3HomogeneousCoefficientFamily

theorem index_card_pos (d : ℕ) : 0 < Fintype.card (Index d) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨Finsupp.single 0 d, Finsupp.degree_single 0 d⟩⟩

theorem monomial_bound (d : ℕ) (m : Index d) (v : Fin 4 → ℤ) (H : ℕ)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) : |m.val.prod (fun i e ↦ v i ^ e)| ≤ (H : ℤ) ^ d := by
  classical
  rw [Finsupp.prod, abs_prod]
  calc
    (∏ i ∈ m.val.support, |v i ^ m.val i|) ≤ ∏ i ∈ m.val.support, (H : ℤ) ^ m.val i := by
      apply Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _)
      intro i _hi
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hv i) _
    _ = (H : ℤ) ^ d := by rw [prod_pow_eq_pow_sum, ← Finsupp.degree_apply, m.property]

theorem evaluation_minors_zero (d : ℕ) (P : MvPolynomial (Fin 4) ℚ)
    (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    (v : Index d → Fin 4 → ℤ) (hv : ∀ i, eval (fun k ↦ (v i k : ℚ)) P = 0) :
    Matrix.det (fun (i j : Index d) ↦ ((j.val.prod (fun k e ↦ v i k ^ e) : ℤ) : ℚ)) = 0 := by
  classical
  let w : Index d → ℚ := fun m ↦ P.coeff m.val
  have hrec : polynomial d w = P := reconstruct d P hP
  have hw : w ≠ 0 := by
    intro hz
    apply hP0
    rw [← hrec, hz]
    simp only [polynomial, Pi.zero_apply, monomial_zero, sum_const_zero]
  let A : Matrix (Index d) (Index d) ℚ :=
    fun i j ↦ ((j.val.prod (fun k e ↦ v i k ^ e) : ℤ) : ℚ)
  have hker : A *ᵥ w = 0 := by
    funext i
    change (∑ j, ((j.val.prod (fun k e ↦ v i k ^ e) : ℤ) : ℚ) * w j) = 0
    have he := evaluation d w (fun k ↦ (v i k : ℚ))
    rw [hrec] at he
    rw [hv i] at he
    convert he.symm using 1
    apply sum_congr rfl
    intro j _hj
    simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow]
  by_contra hdet
  exact hw (Matrix.eq_zero_of_mulVec_eq_zero hdet hker)

theorem exists_bounded_equation (d H : ℕ) (hH : 1 ≤ H) (U : Finset (Fin 4 → ℤ))
    (hheight : ∀ v ∈ U, ∀ i, |v i| ≤ (H : ℤ))
    (P : MvPolynomial (Fin 4) ℚ) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    (hroots : ∀ v ∈ U, eval (fun k ↦ (v k : ℚ)) P = 0) :
    ∃ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous d ∧ Q ≠ 0 ∧
      (∀ m, |Q.coeff m| ≤ (((3 * Fintype.card (Index d) * H ^ d) ^
        (Fintype.card (Index d) - 1) : ℕ) : ℤ)) ∧ ∀ v ∈ U, eval v Q = 0 := by
  classical
  let A : U → Index d → ℤ := fun v m ↦ m.val.prod (fun i e ↦ v.val i ^ e)
  have hA (v : U) (m : Index d) : |A v m| ≤ ((H ^ d : ℕ) : ℤ) := by
    simpa only [Nat.cast_pow] using monomial_bound d m v.val H (hheight v.val v.property)
  have hminor (f : Index d → U) : Matrix.det (fun i j ↦ (A (f i) j : ℚ)) = 0 :=
    evaluation_minors_zero d P hP hP0 (fun i ↦ (f i).val) (fun i ↦ hroots _ (f i).property)
  obtain ⟨w, hw0, hw, hzero⟩ := FiniteRowKernel.exists_integer_annihilator (H ^ d)
    (pow_pos (by omega : 0 < H) d) (index_card_pos d) A hA hminor
  refine ⟨polynomial d w, homogeneous d w, nonzero d w hw0, ?_, ?_⟩
  · intro m
    by_cases hm : m.degree = d
    · change |(polynomial d w).coeff (⟨m, hm⟩ : Index d).val| ≤ _
      rw [coeff_index]
      exact hw ⟨m, hm⟩
    · rw [coeff_outside d w m hm, abs_zero]
      positivity
  · intro v hv
    rw [evaluation]
    exact hzero ⟨v, hv⟩

end PaperP1.P3HomogeneousIntegerInterpolation
