module

public import PaperP1.Geometry.ProjectiveCurveData
public import PaperP1.Algebra.IntegerLinearHilbertSlope
public import PaperP1.Algebra.GradedLinearHilbertSection

/-! # Intrinsic positive integer degree and actual section dimensions of projective curve ideals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveCurveHilbertDegree

open Polynomial ProjectiveCurveData

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_nat_degree {σ : Type} (Γ : Curve σ) :
    ∃ d : ℕ, 0 < d ∧ (d : ℚ) = Γ.degree := by
  obtain ⟨N, hN⟩ := Γ.hilbert
  obtain ⟨d, hd, hdegree, _hinc⟩ := IntegerLinearHilbertSlope.slope_and_increment
    (fun n ↦ Module.finrank ℚ (piece Γ.ideal n)) Γ.degree Γ.constant Γ.degree_pos N (by
      intro n hn
      simpa only [eval_add, eval_mul, eval_C, eval_X] using hN n hn)
  exact ⟨d, hd, hdegree⟩

def natDegree {σ : Type} (Γ : Curve σ) : ℕ := (exists_nat_degree Γ).choose

theorem natDegree_pos {σ : Type} (Γ : Curve σ) : 0 < natDegree Γ :=
  (exists_nat_degree Γ).choose_spec.1

theorem natDegree_cast {σ : Type} (Γ : Curve σ) : (natDegree Γ : ℚ) = Γ.degree :=
  (exists_nat_degree Γ).choose_spec.2

theorem eventual_increment {σ : Type} (Γ : Curve σ) :
    ∃ N : ℕ, ∀ n ≥ N,
      Module.finrank ℚ (piece Γ.ideal (n + 1)) = Module.finrank ℚ (piece Γ.ideal n) + natDegree Γ := by
  obtain ⟨N, hN⟩ := Γ.hilbert
  refine ⟨N, ?_⟩
  intro n hn
  have h₀ := hN n hn
  have h₁ := hN (n + 1) (by omega)
  simp only [eval_add, eval_mul, eval_C, eval_X, Nat.cast_add, Nat.cast_one] at h₀ h₁
  have hd := natDegree_cast Γ
  have heq : (Module.finrank ℚ (piece Γ.ideal (n + 1)) : ℚ) =
      (Module.finrank ℚ (piece Γ.ideal n) : ℚ) + (natDegree Γ : ℚ) := by
    nlinarith only [h₀, h₁, hd]
  exact_mod_cast heq

theorem section_dimension {σ : Type} (Γ : Curve σ) {e : ℕ}
    (f : MvPolynomial σ ℚ) (hf : f.IsHomogeneous e) (hnot : f ∉ Γ.ideal) :
    ∃ N : ℕ, ∀ n ≥ N,
      Module.finrank ℚ (HomogeneousPrincipalQuotient.piece (piece Γ.ideal)
        (Ideal.Quotient.mk Γ.ideal f) (n + e)) = e * natDegree Γ := by
  let : Γ.ideal.IsPrime := Γ.prime
  let : GradedAlgebra (piece Γ.ideal) := HomogeneousQuotientGrading.grading
    (MvPolynomial.homogeneousSubmodule σ ℚ) Γ.ideal Γ.homogeneous
  have hf' : Ideal.Quotient.mk Γ.ideal f ∈ piece Γ.ideal e :=
    Submodule.mem_map.mpr ⟨f, hf, rfl⟩
  have hf0 : Ideal.Quotient.mk Γ.ideal f ≠ 0 := fun he ↦ hnot (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have hp : GradedHilbertPolynomial.IsHilbertPolynomial (piece Γ.ideal)
      (C (natDegree Γ : ℚ) * X + C Γ.constant) := by
    rw [natDegree_cast Γ]
    exact Γ.hilbert
  exact GradedLinearHilbertSection.eventual_dimension (piece Γ.ideal) (natDegree Γ)
    (natDegree_pos Γ) Γ.constant hp hf' hf0

end PaperP1.ProjectiveCurveHilbertDegree
