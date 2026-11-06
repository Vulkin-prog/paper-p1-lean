module

public import PaperP1.Diophantine.GraphPlaneAverageUpperBound
public import Mathlib.Analysis.Real.Sqrt

/-! # Two explicit unproved classical plane-section inputs, independent of the surface point-count target

These are definitions of hypotheses. Neither general proposition is asserted here.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3ClassicalPlanePointInputs

open MvPolynomial P3GraphPlaneSection GraphPlanePointCounts

def PlaneCurveUpperBound (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ K₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), K₀ ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ Q : MvPolynomial (Fin 3) (ZMod p), Q.IsHomogeneous d →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) Q) →
      ((affineZeros Q).card : ℝ) ≤ (p : ℝ) + C * Real.sqrt p

def GoodGraphSection (d : ℕ) : Prop :=
  ∃ K₀ : ℕ, ∀ (p : ℕ) (hp : p.Prime), K₀ ≤ p →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ P : MvPolynomial (Fin 4) (ZMod p), P.IsHomogeneous d →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P) →
      ∃ a : Fin 3 → AlgebraicClosure (ZMod p),
        Irreducible (planeSection a (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) P))

end PaperP1.P3ClassicalPlanePointInputs
