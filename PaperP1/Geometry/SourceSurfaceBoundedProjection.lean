module

public import PaperP1.Geometry.FiniteIndexHomogeneousProjection
public import PaperP1.Algebra.SourceSurfacePowerParameters
public import PaperP1.Geometry.SourceProjectiveEmbedding

/-! # The actual chosen source surface has a uniformly bounded integer birational projection into P³ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceBoundedProjection

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese
  SourceVeroneseGrading SourceProjectiveEmbedding LinearHypersurfaceImage

def coefficientBound (k D : ℕ) : ℕ :=
  (((D + 2).choose 2 + k - 1) * (2 ^ k * D ^ 2) ^ 2 + 1) ^
    ((D + 2).choose 2 + k - 1)

def heightFactor (k D : ℕ) : ℕ := ((D + 2).choose 2 + k) * coefficientBound k D

theorem coefficientBound_pos (k D : ℕ) : 0 < coefficientBound k D := by
  exact pow_pos (by omega) _

theorem heightFactor_pos (k D : ℕ) : 0 < heightFactor k D := by
  apply Nat.mul_pos
  · exact (Nat.choose_pos (by omega : 2 ≤ D + 2)).trans_le (Nat.le_add_right _ _)
  · exact coefficientBound_pos k D

def primitive {F : Type*} {ι : Type} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    [Fintype (GeneratorIndex F ι D)] (u : GeneratorIndex F ι D → ℕ) : veronese c D I J :=
  aeval (R := F) (sourceGenerator c D I J) (CommonLinearNormalization.form (fun i ↦ (u i : F)))

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (HomogeneousSplitRadicalRelations.WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] [CharZero F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

local instance indexFinite : Finite (GeneratorIndex F (Fin s.length) D) := index_finite F (Fin s.length) D
local instance indexFintype : Fintype (GeneratorIndex F (Fin s.length) D) := Fintype.ofFinite _

include hdeg in
theorem exists_projection
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    ∃ (u : GeneratorIndex F (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) F)
        (δ : veronese c D I J),
      (∀ i, u i ≤ coefficientBound s.length D) ∧
      let g := SourceSurfacePowerParameters.parameters s c D hD I J hs;
      let y := primitive c D I J u;
      ideal (F := F) g y = Ideal.span {q} ∧ Irreducible q ∧
      q.IsHomogeneous (2 ^ s.length * D ^ 2) ∧ q.totalDegree = 2 ^ s.length * D ^ 2 ∧
      (finSuccEquiv F 3 q).Monic ∧
      (letI : Algebra (CoordinateRing (F := F) g y) (veronese c D I J) :=
          (toSource g y).toRingHom.toAlgebra;
        Module.finrank (CoordinateRing (F := F) g y) (veronese c D I J) = 1) ∧
      δ = aeval (R := F) (coordinates g y) (pderiv 0 q) ∧
      δ ∈ sourcePiece c D I J (2 ^ s.length * D ^ 2 - 1) ∧ δ ≠ 0 ∧
      (∀ a : veronese c D I J, δ * a ∈ (toSource (F := F) g y).range) ∧
      ∀ (N : ℕ) (v : GeneratorIndex F (Fin s.length) D → ℤ), (∀ i, (v i).natAbs ≤ N) →
        |eval v (CommonLinearNormalization.form (fun i ↦ (u i : ℤ)))| ≤
          ((heightFactor s.length D * N : ℕ) : ℤ) := by
  let := sourceGrading c D I J hdeg hD
  let := source_isDomain s c D I J hs hc hne hI hJ
  have hd : 0 < 2 ^ s.length * D ^ 2 := mul_pos (pow_pos (by decide) _) (pow_pos hD _)
  have hh := FiniteIndexHomogeneousProjection.exists_projection (sourcePiece c D I J)
    (sourceGenerator c D I J) (sourceGenerator_mem_one c D I J)
    (SourceVeroneseIrrelevant.source_generators_adjoin_top c D hD I J)
    (SourceSurfacePowerParameters.parameters s c D hD I J hs)
    (SourceSurfacePowerParameters.parameter_mem s c D hD I J hs)
    (SourceSurfacePowerParameters.finite s c D hD I J hs hdeg)
    (SourceSurfacePowerParameters.injective s c D hD I J hs)
    (2 ^ s.length * D ^ 2) hd (SourceSurfacePowerParameters.rank s c D hD I J hs hdeg hc hne hI hJ)
  obtain ⟨u, q, δ, hu, hq, hirr, hhom, htotal, hmonic, hrank, hpartial, hδmem, hδ0, hconductor, hheight⟩ := hh
  refine ⟨u, q, δ, ?_, hq, hirr, hhom, htotal, hmonic, hrank, hpartial, hδmem, hδ0, hconductor, ?_⟩
  · simpa only [coordinate_count_fin, coefficientBound] using hu
  · simpa only [coordinate_count_fin, heightFactor, coefficientBound] using hheight

end PaperP1.SourceSurfaceBoundedProjection
