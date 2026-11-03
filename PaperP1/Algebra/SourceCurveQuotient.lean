module

public import PaperP1.Algebra.GradedQuotientModuleGenerators
public import PaperP1.Algebra.FiniteGradedLinearGrowth
public import PaperP1.Algebra.SourceVeroneseScalars
public import PaperP1.Algebra.SourceVeroneseHomogeneousBasis
public import PaperP1.Algebra.SourceVeroneseHilbert
public import PaperP1.Algebra.StandardVeroneseHilbert

/-! # Actual homogeneous prime quotients of the manuscript source and their base-module growth -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceCurveQuotient

open Module Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.SourceVeroneseGradedBaseMap
  PaperP1.FiniteQuadraticTower PaperP1.QuadraticTowerHomogeneousBasis

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)
  (P : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J))

def baseIdeal : Ideal (Base F D) :=
  GradedQuotientModuleGenerators.baseIdeal (gradedBaseMap s c D hD I J hs) P

abbrev SourceRing := HomogeneousSplitRadicalVeronese.veronese c D I J ⧸ P
abbrev BaseRing := Base F D ⧸ baseIdeal s c D I J hs hD P

local instance sourceQuotientRing : CommRing (SourceRing s c D I J P) := inferInstance
local instance baseQuotientRing : CommRing (BaseRing s c D I J hs hD P) := inferInstance
local instance sourceQuotientSemiring : Semiring (SourceRing s c D I J P) :=
  (inferInstance : CommSemiring (SourceRing s c D I J P)).toSemiring
local instance baseQuotientSemiring : Semiring (BaseRing s c D I J hs hD P) :=
  (inferInstance : CommSemiring (BaseRing s c D I J hs hD P)).toSemiring
local instance quotientModule [Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P)] :
    Module (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) := Algebra.toModule

def sourcePiece (n : ℕ) : Submodule F (SourceRing s c D I J P) :=
  HomogeneousQuotientGrading.piece (SourceVeroneseGrading.sourcePiece c D I J) P n

def basePiece (n : ℕ) : Submodule F (BaseRing s c D I J hs hD P) :=
  HomogeneousQuotientGrading.piece (SourceVeroneseGrading.nativePiece F D)
    (baseIdeal s c D I J hs hD P) n

def map : basePiece s c D I J hs hD P →+*ᵍ sourcePiece s c D I J P :=
  GradedQuotientModuleGenerators.map (gradedBaseMap s c D hD I J hs) P

def ringMap : BaseRing s c D I J hs hD P →+* SourceRing s c D I J P :=
  (map s c D I J hs hD P).toRingHom

def rank : ℕ := by
  letI : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  exact Module.finrank (BaseRing s c D I J hs hD P) (SourceRing s c D I J P)

theorem map_injective : Function.Injective (map s c D I J hs hD P) :=
  GradedQuotientModuleGenerators.map_injective (gradedBaseMap s c D hD I J hs) P

theorem map_commutes (a : F) :
    ringMap s c D I J hs hD P (algebraMap F (BaseRing s c D I J hs hD P) a) =
      @algebraMap F (SourceRing s c D I J P) inferInstance
        (inferInstance : Semiring (SourceRing s c D I J P)) inferInstance a :=
  GradedQuotientModuleGenerators.map_commutes (gradedBaseMap s c D hD I J hs)
    (SourceVeroneseScalars.standardBaseMap_commutes s c D hD I J hs) P a

theorem base_piece_finite (n : ℕ) : Module.Finite F (basePiece s c D I J hs hD P n) := by
  have := StandardVeroneseHilbert.piece_finite F D n
  exact HomogeneousQuotientGrading.piece_finite (SourceVeroneseGrading.nativePiece F D)
    (baseIdeal s c D I J hs hD P) n

theorem base_domain [P.IsPrime] : IsDomain (BaseRing s c D I J hs hD P) := by
  change IsDomain (Base F D ⧸ P.comap (gradedBaseMap s c D hD I J hs).toRingHom)
  infer_instance

theorem source_domain [P.IsPrime] : IsDomain (SourceRing s c D I J P) := by infer_instance

variable (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

include hdeg hD in
theorem baseIdeal_homogeneous
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) :
    letI := SourceVeroneseGrading.nativeGrading F D hD
    (baseIdeal s c D I J hs hD P).IsHomogeneous (SourceVeroneseGrading.nativePiece F D) := by
  let := SourceVeroneseGrading.nativeGrading F D hD
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact GradedQuotientModuleGenerators.baseIdeal_homogeneous (gradedBaseMap s c D hD I J hs) P hP

@[instance_reducible] def baseGrading
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) :
    GradedAlgebra (basePiece s c D I J hs hD P) := by
  letI := SourceVeroneseGrading.nativeGrading F D hD
  exact HomogeneousQuotientGrading.grading (SourceVeroneseGrading.nativePiece F D)
    (baseIdeal s c D I J hs hD P) (baseIdeal_homogeneous s c D I J hs hD P hdeg hP)

@[instance_reducible] def sourceGrading
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) :
    GradedAlgebra (sourcePiece s c D I J P) := by
  letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  exact HomogeneousQuotientGrading.grading (SourceVeroneseGrading.sourcePiece c D I J) P hP

abbrev GeneratorIndex := Index (RelativeVeroneseMap.radicands s c D I J hdeg)

def generator (i : GeneratorIndex s c D I J hdeg) : SourceRing s c D I J P :=
  Ideal.Quotient.mk P (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD i)

def weight (i : GeneratorIndex s c D I J hdeg) : ℕ :=
  indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i

theorem generator_mem (i : GeneratorIndex s c D I J hdeg) :
    generator s c D I J hs hD P hdeg i ∈ sourcePiece s c D I J P (weight s c D I J hdeg i) := by
  exact Submodule.mem_map.mpr ⟨RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD i,
    SourceVeroneseHomogeneousBasis.sourceBasis_mem s c D I J hdeg hs hD i, rfl⟩

theorem generators : ∀ b : SourceRing s c D I J P,
    ∃ a : GeneratorIndex s c D I J hdeg → BaseRing s c D I J hs hD P,
      ∑ i, map s c D I J hs hD P (a i) * generator s c D I J hs hD P hdeg i = b := by
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (gradedBaseMap s c D hD I J hs).toRingHom.toAlgebra
  exact GradedQuotientModuleGenerators.generators (gradedBaseMap s c D hD I J hs) P
    (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD)
    (GradedModulePieceMap.generators_of_span (gradedBaseMap s c D hD I J hs)
      (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD)
      (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD).span_eq)

theorem generators_span :
    letI : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
      (ringMap s c D I J hs hD P).toAlgebra
    Submodule.span (BaseRing s c D I J hs hD P)
      (Set.range (generator s c D I J hs hD P hdeg)) = ⊤ := by
  let : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  apply top_unique
  intro b _
  apply (Submodule.mem_span_range_iff_exists_fun _).mpr
  exact generators s c D I J hs hD P hdeg b

include hdeg hs hD in
theorem source_piece_finite (n : ℕ) : Module.Finite F (sourcePiece s c D I J P n) := by
  have := SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  exact HomogeneousQuotientGrading.piece_finite (SourceVeroneseGrading.sourcePiece c D I J) P n

include hdeg in
theorem rank_bounds [P.IsPrime] : 1 ≤ rank s c D I J hs hD P ∧
    rank s c D I J hs hD P ≤ 2 ^ s.length := by
  let : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  have := base_domain s c D I J hs hD P
  have := source_domain s c D I J P
  have hgen := generators_span s c D I J hs hD P hdeg
  have : Module.Finite (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    FreeApproximationRank.finite_of_span (generator s c D I J hs hD P hdeg) hgen
  constructor
  · have h := LinearMap.finrank_le_finrank_of_injective
      (f := Algebra.linearMap (BaseRing s c D I J hs hD P) (SourceRing s c D I J P))
      (map_injective s c D I J hs hD P)
    simpa only [Module.finrank_self, rank] using h
  · have h := finrank_le_of_span_eq_top hgen
    simpa only [rank, GeneratorIndex, index_card, RelativeVeroneseMap.radicands_length] using h

theorem hasSlope [P.IsPrime]
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) (a b : ℚ)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (basePiece s c D I J hs hD P)
      (Polynomial.C a * Polynomial.X + Polynomial.C b)) :
    LinearHilbertGrowth.HasSlope (LinearHilbertGrowth.function (sourcePiece s c D I J P))
      ((rank s c D I J hs hD P : ℚ) * a) := by
  let : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  let := baseGrading s c D I J hs hD P hdeg hP
  let := sourceGrading s c D I J hD P hdeg hP
  have := base_domain s c D I J hs hD P
  have := source_domain s c D I J P
  exact FiniteGradedLinearGrowth.hasSlope (map s c D I J hs hD P)
    (map_commutes s c D I J hs hD P) (generator s c D I J hs hD P hdeg)
    (weight s c D I J hdeg) (generator_mem s c D I J hs hD P hdeg)
    (map_injective s c D I J hs hD P) (generators_span s c D I J hs hD P hdeg)
    (base_piece_finite s c D I J hs hD P) a b hp

theorem multiplicity [P.IsPrime]
    (hP : letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
      P.IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J)) (a b : ℚ) (ha : 0 < a)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (basePiece s c D I J hs hD P)
      (Polynomial.C a * Polynomial.X + Polynomial.C b))
    (hB : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial (sourcePiece s c D I J P) p) :
    GradedHilbertPolynomial.multiplicity (sourcePiece s c D I J P) hB =
      (rank s c D I J hs hD P : ℚ) * a := by
  let : Algebra (BaseRing s c D I J hs hD P) (SourceRing s c D I J P) :=
    (ringMap s c D I J hs hD P).toAlgebra
  let := baseGrading s c D I J hs hD P hdeg hP
  let := sourceGrading s c D I J hD P hdeg hP
  have := base_domain s c D I J hs hD P
  have := source_domain s c D I J P
  exact FiniteGradedLinearGrowth.multiplicity (map s c D I J hs hD P)
    (map_commutes s c D I J hs hD P) (generator s c D I J hs hD P hdeg)
    (weight s c D I J hdeg) (generator_mem s c D I J hs hD P hdeg)
    (map_injective s c D I J hs hD P) (generators_span s c D I J hs hD P hdeg)
    (base_piece_finite s c D I J hs hD P) a b ha hp hB

end PaperP1.SourceCurveQuotient
