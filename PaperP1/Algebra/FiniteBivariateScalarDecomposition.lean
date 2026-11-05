module

public import PaperP1.Algebra.PolynomialScalarProjection
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact finite scalar decomposition of every extension-field bivariate polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteBivariateScalarDecomposition

open Polynomial Finset Module PaperP1.PolynomialScalarProjection

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

def coordinate (b : Basis ι K L) (i : ι) : L →ₗ[K] K :=
  (Finsupp.lapply i).comp b.repr.toLinearMap

theorem coordinate_apply (b : Basis ι K L) (i : ι) (c : L) :
    coordinate b i c = b.repr c i := rfl

def componentIndices (b : Basis ι K L) (P : L[X][X]) : Finset ι := by
  classical
  exact P.support.biUnion (fun n ↦ (P.coeff n).support.biUnion
    (fun m ↦ (b.repr ((P.coeff n).coeff m)).support))

theorem coefficient_support_subset (b : Basis ι K L) (P : L[X][X]) (n m : ℕ) :
    (b.repr ((P.coeff n).coeff m)).support ⊆ componentIndices b P := by
  classical
  intro i hi
  have hrepr := Finsupp.mem_support_iff.mp hi
  have hnm : (P.coeff n).coeff m ≠ 0 := by
    intro hz
    apply hrepr
    simp only [hz, map_zero, Finsupp.zero_apply]
  have hn : P.coeff n ≠ 0 := by
    intro hz
    exact hnm (by simp only [hz, coeff_zero])
  exact mem_biUnion.mpr ⟨n, Polynomial.mem_support_iff.mpr hn,
    mem_biUnion.mpr ⟨m, Polynomial.mem_support_iff.mpr hnm, hi⟩⟩

theorem component_zero_of_not_mem (b : Basis ι K L) (P : L[X][X]) (i : ι)
    (hi : i ∉ componentIndices b P) : component (coordinate b i) P = 0 := by
  classical
  apply Polynomial.ext
  intro n
  apply Polynomial.ext
  intro m
  simp only [component_coefficient, coordinate_apply, coeff_zero]
  apply Finsupp.notMem_support_iff.mp
  intro hmem
  exact hi (coefficient_support_subset b P n m hmem)

theorem reconstruction (b : Basis ι K L) (P : L[X][X]) :
    (∑ i ∈ componentIndices b P, C (C (b i)) *
      extend (L := L) (component (coordinate b i) P)) = P := by
  classical
  apply Polynomial.ext
  intro n
  apply Polynomial.ext
  intro m
  simp only [finsetSum_coeff, coeff_C_mul, extend_coefficient,
    component_coefficient, coordinate_apply]
  have hsum : (∑ i ∈ (b.repr ((P.coeff n).coeff m)).support,
      b i * algebraMap K L (b.repr ((P.coeff n).coeff m) i)) =
      (∑ i ∈ componentIndices b P, b i * algebraMap K L (b.repr ((P.coeff n).coeff m) i)) := by
    apply sum_subset (coefficient_support_subset b P n m)
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, map_zero, mul_zero]
  rw [← hsum]
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def, mul_comm] using
    b.linearCombination_repr ((P.coeff n).coeff m)

end PaperP1.FiniteBivariateScalarDecomposition
