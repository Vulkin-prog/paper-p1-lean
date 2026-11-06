module

public import PaperP1.Algebra.SourceSurfacePowerParameters
public import PaperP1.Algebra.SplitWeightedGeneratorIndex

/-! # The finite source normalization coordinates are literal chosen-embedding coordinate indices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfacePowerCoordinates

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalRelations
  HomogeneousSplitRadicalGrading HomogeneousSplitRadicalFiniteVeronese SourceVeroneseGrading

def index (F ι : Type*) [Field F] (D : ℕ) (j : Fin 3) :
    SplitWeightedDegreeGenerators.generators F ι D :=
  SplitWeightedGeneratorIndex.indexEquiv F ι D (Sum.inl
    ⟨Finsupp.single j D, by rw [Finsupp.degree_single]⟩)

theorem generator_eq {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (j : Fin 3) :
    sourceGenerator c D I J (index F (Fin s.length) D j) =
      SourceSurfacePowerParameters.parameters s c D hD I J hs j := by
  apply Subtype.ext
  change quotientMap c D I J (rename Sum.inl (monomial (Finsupp.single j D) 1)) =
    HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J (X j ^ D)
  rw [X_pow_eq_monomial]
  rfl

end PaperP1.SourceSurfacePowerCoordinates
