module

public import PaperP1.Algebra.IrrelevantGenerated
public import PaperP1.Algebra.SourceVeroneseGradedBaseMap
public import PaperP1.Algebra.HomogeneousSplitRadicalVeroneseTowerData

/-! # The actual source irrelevant ideal lies in the radical of the mapped base irrelevant ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseIrrelevant

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalVeronese
  PaperP1.HomogeneousSplitRadicalFiniteVeronese PaperP1.HomogeneousSplitRadicalBaseInjection
  PaperP1.HomogeneousSplitRadicalVeroneseTowerData PaperP1.HomogeneousSplitRadicalPolynomials
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def nativeIrrelevant (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) : Ideal (Base F D) := by
  let := nativeGrading F D hD
  exact (HomogeneousIdeal.irrelevant (nativePiece F D)).toIdeal

def sourceIrrelevant {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) : Ideal (veronese c D I J) := by
  let := sourceGrading c D I J hdeg hD
  exact (HomogeneousIdeal.irrelevant (sourcePiece c D I J)).toIdeal

theorem source_generators_adjoin_top {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ) :
    Algebra.adjoin F (Set.range (sourceGenerator c D I J)) = ⊤ := by
  let S := veronese c D I J
  let T := Algebra.adjoin F (Set.range (sourceGenerator c D I J))
  have hST : S ≤ T.map S.val := by
    apply (generated_by_source_generators c D hD I J).le.trans
    apply Algebra.adjoin_le
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨sourceGenerator c D I J ⟨p, hp⟩,
      Algebra.subset_adjoin (show sourceGenerator c D I J ⟨p, hp⟩ ∈ Set.range (sourceGenerator c D I J) from
        ⟨⟨p, hp⟩, rfl⟩), rfl⟩
  change T = ⊤
  apply top_unique
  intro x _hx
  obtain ⟨y, hy, hxy⟩ := hST x.property
  exact (show y = x from Subtype.ext hxy) ▸ hy

theorem native_homogeneous_mem_irrelevant (F : Type*) [Field F] (D : ℕ) (hD : 0 < D)
    (n : ℕ) (hn : 0 < n) (p : Base F D) (hp : (p : MvPolynomial (Fin 3) F).IsHomogeneous (n * D)) :
    p ∈ nativeIrrelevant F D hD := by
  let := nativeGrading F D hD
  exact HomogeneousIdeal.mem_irrelevant_of_mem (nativePiece F D) hn hp

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)

def mappedIdeal
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    Ideal (veronese c D I J) := (nativeIrrelevant F D hD).map (gradedBaseMap s c D hD I J hs).toRingHom

theorem radical_square_mem_map
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (i : Fin s.length) :
    radical c D I J i ^ 2 ∈ mappedIdeal s c D hD I J hs := by
  let b := baseRadicand (c i) D (I i) (J i) (hdeg i)
  have hb0 : (b : MvPolynomial (Fin 3) F).IsHomogeneous (2 * D) := by
    change (nativeRadicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)).IsHomogeneous (2 * D)
    have hi := hdeg i
    convert nativeRadicand_homogeneous (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i) using 1; omega
  have hb := native_homogeneous_mem_irrelevant F D hD 2 (by decide) b hb0
  have hf := Ideal.mem_map_of_mem (gradedBaseMap s c D hD I J hs).toRingHom hb
  have he : gradedBaseMap s c D hD I J hs b = radical c D I J i ^ 2 := by
    apply Subtype.ext
    change basePolynomialMap c D I J (b : MvPolynomial (Fin 3) F) =
      (radical c D I J i : CoordinateRing c D I J) ^ 2
    rw [radical_square]
    rfl
  exact he ▸ hf

theorem pure_generator_mem_map
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (p : SplitWeightedDegreeGenerators.generators F (Fin s.length) D)
    (hp : (p : WeightedPolynomial F (Fin s.length)) ∈ SplitWeightedDegreeGenerators.baseMonomials F (Fin s.length) D) :
    sourceGenerator c D I J p ∈ mappedIdeal s c D hD I J hs := by
  rw [StandardBaseVeronese.baseMonomials_eq_image] at hp
  obtain ⟨q, hq, hqp⟩ := hp
  have hqm : q.IsHomogeneous D := by
    obtain ⟨d, hd, hqd⟩ := hq
    rw [← hqd]
    exact MvPolynomial.isHomogeneous_monomial 1 hd
  let b : Base F D := ⟨q, by
    change q ∈ StandardBaseVeronese.nativeVeronese F D
    rw [StandardBaseVeronese.nativeVeronese_eq_adjoin F D hD]
    exact Algebra.subset_adjoin hq⟩
  have hb := native_homogeneous_mem_irrelevant F D hD 1 (by decide) b
    (by simpa only [one_mul] using hqm)
  have hf := Ideal.mem_map_of_mem (gradedBaseMap s c D hD I J hs).toRingHom hb
  have he : gradedBaseMap s c D hD I J hs b = sourceGenerator c D I J p := by
    apply Subtype.ext
    change quotientMap c D I J (MvPolynomial.rename Sum.inl q) = quotientMap c D I J (p : WeightedPolynomial F (Fin s.length))
    rw [hqp]
  exact he ▸ hf

theorem source_irrelevant_le_radical
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    sourceIrrelevant c D I J hdeg hD ≤ (mappedIdeal s c D hD I J hs).radical := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  apply IrrelevantGenerated.irrelevant_le_radical (sourcePiece c D I J)
    (Set.range (sourceGenerator c D I J))
    (by rintro _ ⟨p, rfl⟩; exact sourceGenerator_mem_one c D I J p)
    (source_generators_adjoin_top c D hD I J) (mappedIdeal s c D hD I J hs)
  rintro _ ⟨p, rfl⟩
  rcases p.property with hpure | ⟨i, hi⟩
  · exact Ideal.le_radical (pure_generator_mem_map s c D hD I J hs p hpure)
  · have he : sourceGenerator c D I J p = radical c D I J i := by
      apply Subtype.ext
      change quotientMap c D I J (p : WeightedPolynomial F (Fin s.length)) = quotientMap c D I J (MvPolynomial.X (Sum.inr i))
      rw [← hi]
    rw [he]
    exact ⟨2, radical_square_mem_map s c D hD I J hs hdeg i⟩

end PaperP1.SourceVeroneseIrrelevant
