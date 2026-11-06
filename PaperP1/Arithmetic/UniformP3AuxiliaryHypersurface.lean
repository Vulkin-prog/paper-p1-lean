module

public import PaperP1.Arithmetic.UniformP3HypersurfaceCover

/-! # The remaining quantitative global auxiliary-hypersurface proposition

`UniformAuxiliary` is an explicit UNPROVED INPUT. It adds no axiom. The property
asks for one homogeneous auxiliary equation vanishing on all actual normalized
integer points, of degree at the classical global determinant scale. It does not
assume a curve family, an exception set or their desired covering estimates.
Compare Salberger, Counting rational points on projective varieties, Theorem1.2:
https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/plms.12508 .
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformP3AuxiliaryHypersurface

open MvPolynomial

def AtDegree (d : ℕ) (B ε : ℝ) : Prop :=
  ∀ q : MvPolynomial (Fin 4) ℚ,
    Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) q) →
    q.IsHomogeneous d → q.totalDegree = d → ∀ H : ℕ, 1 ≤ H →
    ∃ (e : ℕ) (G : MvPolynomial (Fin 4) ℚ), G.IsHomogeneous e ∧ ¬ q ∣ G ∧
      (e : ℝ) ≤ B * (H : ℝ) ^ (1 / Real.sqrt (d : ℝ) + ε) ∧
      ∀ v ∈ UniformP3HypersurfaceCover.points q H, eval (fun j ↦ (v j : ℚ)) G = 0

def UniformAuxiliary (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ AtDegree d B ε

end PaperP1.UniformP3AuxiliaryHypersurface
