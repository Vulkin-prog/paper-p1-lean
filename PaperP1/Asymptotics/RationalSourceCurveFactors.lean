module

public import PaperP1.Algebra.RationalBivariateIrreducibility
public import PaperP1.Asymptotics.ConstructedClusterCurveData

/-! # Every factor in the actual source curve cover is irreducible over the rationals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalSourceCurveFactors

open Finset Polynomial PaperP1.TwoKernelDeterminantBoxes PaperP1.ConstructedClusterCurveData
open PaperP1.RationalBivariateIrreducibility

theorem local_cover_factors {N κ Amax Bmax : ℕ} {Q : Finset Quad}
    {B₀ B₁ : Matrix (Fin 2) (Fin 2) ℤ} {L T : ℝ} {F : Bool × Bool → Finset ℤ[X][X]}
    (h : LocalCover N κ Amax Bmax Q B₀ B₁ L T F) :
    ∀ c : Bool × Bool, ∀ G ∈ F c, Irreducible (rationalize G) := by
  intro c G hG
  have hf := (h.factors c).2.1 G hG
  exact rational_irreducible G hf.1 hf.2.1

end PaperP1.RationalSourceCurveFactors
