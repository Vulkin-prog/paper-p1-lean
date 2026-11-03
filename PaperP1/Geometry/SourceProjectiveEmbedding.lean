module

public import PaperP1.Algebra.GradedPolynomialGenerators
public import PaperP1.Geometry.ProjSurjectiveClosedImmersion
public import PaperP1.Geometry.SourceProjectiveMap
public import PaperP1.Algebra.SourceVeroneseIrrelevant
public import PaperP1.Algebra.SplitWeightedGeneratorIndex

/-! # The actual source embeds by its literal degree-D monomials and radical coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.SourceProjectiveEmbedding

open AlgebraicGeometry PaperP1.HomogeneousSplitRadicalRelations PaperP1.SourceVeroneseGrading

attribute [local instance] MvPolynomial.gradedAlgebra

local instance weightedRing (F : Type u) (ι : Type) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

abbrev GeneratorIndex (F : Type u) [Field F] (ι : Type) (D : ℕ) :=
  SplitWeightedDegreeGenerators.generators F ι D

theorem index_finite (F : Type u) [Field F] (ι : Type) [Finite ι] (D : ℕ) :
    Finite (GeneratorIndex F ι D) := (SplitWeightedDegreeGenerators.generators_finite F ι D).to_subtype

theorem coordinate_count (F : Type u) [Field F] (ι : Type) [Finite ι] (D : ℕ) :
    Nat.card (GeneratorIndex F ι D) = (D + 2).choose 2 + Nat.card ι :=
  SplitWeightedGeneratorIndex.index_card F ι D

theorem coordinate_count_fin (F : Type u) [Field F] (k D : ℕ) :
    Nat.card (GeneratorIndex F (Fin k) D) = (D + 2).choose 2 + k := by
  rw [coordinate_count, Nat.card_fin]

def ambientScheme (F : Type u) [Field F] (ι : Type) (D : ℕ) : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule (GeneratorIndex F ι D) F)

variable {F : Type u} [Field F] {ι : Type}
  (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D)

def evaluation :
    MvPolynomial.homogeneousSubmodule (GeneratorIndex F ι D) F →+*ᵍ sourcePiece c D I J := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.gradedEval (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J)

theorem evaluation_X (i : GeneratorIndex F ι D) :
    evaluation c D I J hdeg hD (MvPolynomial.X i) = sourceGenerator c D I J i := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.gradedEval_X (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) i

theorem evaluation_surjective : Function.Surjective (evaluation c D I J hdeg hD) := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.eval_surjective (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J)

theorem irrelevant_le_map :
    letI := sourceGrading c D I J hdeg hD
    (HomogeneousIdeal.irrelevant (sourcePiece c D I J)).toIdeal ≤
      ((HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (GeneratorIndex F ι D) F)).toIdeal.map
        (evaluation c D I J hdeg hD).toRingHom) := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.irrelevant_le_map (sourcePiece c D I J) (sourceGenerator c D I J)
    (sourceGenerator_mem_one c D I J) (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J)

def embedding : SourceProjectiveMap.sourceScheme c D I J hdeg hD ⟶ ambientScheme F ι D := by
  let := sourceGrading c D I J hdeg hD
  exact ProjRadicalMap.map (evaluation c D I J hdeg hD) ((irrelevant_le_map c D I J hdeg hD).trans Ideal.le_radical)

theorem embedding_closedImmersion : IsClosedImmersion (embedding c D I J hdeg hD) := by
  let := sourceGrading c D I J hdeg hD
  apply ProjSurjectiveClosedImmersion.map_closedImmersion (evaluation c D I J hdeg hD)
    ((irrelevant_le_map c D I J hdeg hD).trans Ideal.le_radical) (evaluation_surjective c D I J hdeg hD)
  rw [IrrelevantGenerated.irrelevant_eq_span
    (MvPolynomial.homogeneousSubmodule (GeneratorIndex F ι D) F)
    (Set.range (MvPolynomial.X (R := F) : GeneratorIndex F ι D → _))
    (by
      rintro x ⟨i, hi⟩
      change x.IsHomogeneous 1
      rw [← hi]
      exact MvPolynomial.isHomogeneous_X F i) (MvPolynomial.adjoin_range_X)]
  apply Ideal.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X F i⟩, rfl⟩

end PaperP1.SourceProjectiveEmbedding
