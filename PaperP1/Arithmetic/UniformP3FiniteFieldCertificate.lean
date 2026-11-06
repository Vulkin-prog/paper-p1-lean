module

public import PaperP1.Arithmetic.P3CoarseCanonicalClassCount
public import PaperP1.Arithmetic.UniformP3AuxiliaryHypersurface

/-! An explicit independent finite-field certificate proposition; no axiom is introduced. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformP3FiniteFieldCertificate

open MvPolynomial
open scoped Classical

def AtDegree (d : ℕ) (D : ℝ) (T N K₀ : ℕ) : Prop :=
  ∀ A : ℕ, 0 < A → ∀ P : MvPolynomial (Fin 4) ℤ,
    Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) P)) →
    P.IsHomogeneous d → (∀ m, |P.coeff m| ≤ (A : ℤ)) →
    ∃ z : ℤ, z ≠ 0 ∧ z.natAbs ≤ T * A ^ N ∧
      ∀ p : ℕ, p.Prime → K₀ ≤ p → ¬(p : ℤ) ∣ z →
        (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2

def UniformBudget (d : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ T N K₀ : ℕ, 0 < T ∧ AtDegree d (1 + η) T N K₀

theorem monotone_budget (d : ℕ) (D D' : ℝ) (hD : D ≤ D') (T N K₀ : ℕ)
    (h : AtDegree d D T N K₀) : AtDegree d D' T N K₀ := by
  intro A hA P hgeom hhom hcoef
  obtain ⟨z, hz, hbound, hclass⟩ := h A hA P hgeom hhom hcoef
  refine ⟨z, hz, hbound, ?_⟩
  intro p hp hK hzdiv
  exact (hclass p hp hK hzdiv).trans (mul_le_mul_of_nonneg_right hD (sq_nonneg (p : ℝ)))

theorem coarse_budget (d : ℕ) : AtDegree d (d : ℝ) 1 0 0 := by
  intro A _hA P _hgeom hhom _hcoef
  refine ⟨1, by norm_num, by simp, ?_⟩
  intro p hp _hK _hzdiv
  exact_mod_cast P3CoarseCanonicalClassCount.cardinality_bound p d hp P hhom

theorem of_degree_le_one (d : ℕ) (hd : d ≤ 1) : UniformBudget d := by
  intro η hη
  refine ⟨1, 0, 0, by norm_num, ?_⟩
  have hdR : (d : ℝ) ≤ 1 := by exact_mod_cast hd
  exact monotone_budget d d (1 + η) (by linarith) 1 0 0 (coarse_budget d)

end PaperP1.UniformP3FiniteFieldCertificate
