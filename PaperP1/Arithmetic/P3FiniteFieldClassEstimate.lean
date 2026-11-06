module

public import PaperP1.Arithmetic.P3CoarseCanonicalClassCount
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The independent leading-coefficient-one finite-field surface estimate

The general estimate is an explicit UNPROVED INPUT. It contains no integer
coefficient-height certificate, global auxiliary equation or point cover.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3FiniteFieldClassEstimate

open MvPolynomial
open scoped Classical

def GeometricReduction (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ) : Prop := by
  let : Fact p.Prime := ⟨hp⟩
  exact Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) (map (Int.castRingHom (ZMod p)) P))

def UniformEstimate (d : ℕ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), K₀ ≤ p →
    ∀ P : MvPolynomial (Fin 4) ℤ, P.IsHomogeneous d → GeometricReduction p hp P →
      (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ (1 + η) * (p : ℝ) ^ 2

theorem of_degree_le_one (d : ℕ) (hd : d ≤ 1) : UniformEstimate d := by
  intro η hη
  refine ⟨0, ?_⟩
  intro p hp _hK P hP _hgeom
  have hb : (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ (d : ℝ) * (p : ℝ) ^ 2 := by
    exact_mod_cast P3CoarseCanonicalClassCount.cardinality_bound p d hp P hP
  have hdR : (d : ℝ) ≤ 1 := by exact_mod_cast hd
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg (p : ℝ)))

end PaperP1.P3FiniteFieldClassEstimate
