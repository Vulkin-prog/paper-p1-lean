module

public import PaperP1.Algebra.OriginalNormalizedSourceRelation
public import PaperP1.Arithmetic.ActualAffineHypersurfacePointCount
public import PaperP1.Arithmetic.CanonicalClassesToMonicHypersurface

/-! # Uniform actual original-model affine solution and canonical smooth-class counts

The cutoff precedes all primes, original source coefficients, bounded branch
supports and actual chosen rational/integer projection models. The original
source relation, normalization, conductor and exhaustive point correspondence
are internal proofs. Only explicit actual good-prime exclusions remain.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.OriginalProjectedModelPointEstimate
open scoped Classical
open Polynomial PaperP1.SourceProjectiveEmbedding
open PaperP1.IntegerProjectedModelNormalization PaperP1.OriginalNormalizedSourceRelation
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

theorem uniform_upper_bound (k D M : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ), s.length = k →
      ∀ (c : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      (PaperP1.SplitBranchPrimeCertificate.support I J).card ≤ M →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ PaperP1.BranchShiftReductionCertificate.certificate
        (PaperP1.SplitBranchPrimeCertificate.support I J) →
      ∀ hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : ℚ)
        (2*D-((I i).card+(J i).card)) (I i) (J i),
      ∀ (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) ℚ),
      PaperP1.LinearHypersurfaceImage.ideal
        (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
        (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q} →
      q.IsHomogeneous (2 ^ s.length * D ^ 2) → (MvPolynomial.finSuccEquiv ℚ 3 q).Monic →
      ∀ a : ℚ, a ≠ 0 → ∀ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous (2 ^ s.length * D ^ 2) →
      MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q →
      ∀ z : ℤ, PaperP1.P3UniversalGoodReduction.Certificate Q z → ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ topCoefficient Q (2 ^ s.length * D ^ 2) →
      let P := PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q (2 ^ s.length * D ^ 2)))
      ((Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p) P) : ℕ) : ℝ) ≤ (1+η)*(p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := PaperP1.ActualAffineHypersurfacePointCount.uniform_upper_bound
    k D M (2 ^ k * D ^ 2) hD η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hsupport hI hJ hne hnot hs u q hideal hq hm a ha Q hQ hmodel z hz hnotz hnotb
  rw [← hlen] at hK
  have hprops := original_good_prime_data s c D hD I J hs u q hideal hq hm a ha Q hQ hmodel
    z hz p hp hnotz hnotb
  exact hK p hp hlarge (fun i ↦ (c i : ZMod p)) I J hsupport hI hJ hne hnot
    (fieldPrimitive (ZMod p) s.length D c I J u)
    (PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q (2 ^ s.length * D ^ 2))))
    hprops.1 hprops.2.2.1 hprops.2.2.2.2 (by rw [hprops.2.1]) (le_of_eq hprops.2.1) hprops.2.2.2.1

theorem uniform_class_upper_bound (k D M : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ), s.length = k →
      ∀ (c : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      (PaperP1.SplitBranchPrimeCertificate.support I J).card ≤ M →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ PaperP1.BranchShiftReductionCertificate.certificate
        (PaperP1.SplitBranchPrimeCertificate.support I J) →
      ∀ hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : ℚ)
        (2*D-((I i).card+(J i).card)) (I i) (J i),
      ∀ (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) ℚ),
      PaperP1.LinearHypersurfaceImage.ideal
        (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
        (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q} →
      q.IsHomogeneous (2 ^ s.length * D ^ 2) → (MvPolynomial.finSuccEquiv ℚ 3 q).Monic →
      ∀ a : ℚ, a ≠ 0 → ∀ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous (2 ^ s.length * D ^ 2) →
      MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q →
      ∀ z : ℤ, PaperP1.P3UniversalGoodReduction.Certificate Q z → ¬ (p : ℤ) ∣ z →
      ¬ (p : ℤ) ∣ topCoefficient Q (2 ^ s.length * D ^ 2) →
      (Fintype.card (PaperP1.P3CanonicalSmoothResidues.Class p Q) : ℝ) ≤ (1+η)*(p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := uniform_upper_bound k D M hD η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hsupport hI hJ hne hnot hs u q hideal hq hm a ha Q hQ hmodel z hz hnotz hnotb
  have hh := hK p hp hlarge s hlen c I J hsupport hI hJ hne hnot hs u q hideal hq hm a ha
    Q hQ hmodel z hz hnotz hnotb
  have hc := PaperP1.CanonicalClassesToMonicHypersurface.cardinality_le p Q
    (topCoefficient Q (2 ^ s.length * D ^ 2))
  have hcR : (Fintype.card (PaperP1.P3CanonicalSmoothResidues.Class p Q) : ℝ) ≤
      (Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p)
        (PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q (2 ^ s.length * D ^ 2))))) : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans hh

end PaperP1.OriginalProjectedModelPointEstimate
