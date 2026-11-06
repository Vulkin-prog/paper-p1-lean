module

public import PaperP1.Arithmetic.BranchModelReductionCertificate
public import PaperP1.Arithmetic.OriginalProjectedModelPointEstimate
public import PaperP1.Arithmetic.ActualAffineHypersurfacePointCount

/-! # A uniform polynomial-height certificate controls the original source-model canonical class count

The threshold and constants precede all original source and model data. Branch
shifts and original integer coefficients are bounded by the same height. The
certificate combines the literal branch and model exclusions. No finite-field
point, conductor, normalization, kernel or point-identification input is assumed.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.OriginalSourceFiniteFieldBudget
open Polynomial PaperP1.SourceProjectiveEmbedding
open PaperP1.IntegerProjectedModelNormalization PaperP1.OriginalNormalizedSourceRelation
open scoped Classical
local instance indexFinite (k D : ℕ) : Finite (GeneratorIndex ℚ (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite ℚ (Fin k) D
local instance indexFintype (k D : ℕ) : Fintype (GeneratorIndex ℚ (Fin k) D) := Fintype.ofFinite _

theorem bounded_uniform_class_count (k D M : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K T N : ℕ, 0 < T ∧ ∀ A : ℕ, 0 < A →
      ∀ s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing ℚ), s.length = k →
      ∀ (c : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
      (PaperP1.SplitBranchPrimeCertificate.support I J).card ≤ M →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      (∀ b ∈ PaperP1.SplitBranchPrimeCertificate.support I J, |b| ≤ (A : ℤ)) →
      ∀ hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : ℚ)
        (2*D-((I i).card+(J i).card)) (I i) (J i),
      ∀ (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (q : MvPolynomial (Fin 4) ℚ),
      PaperP1.LinearHypersurfaceImage.ideal
        (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : ℚ)) D hD I J hs)
        (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : ℚ)) D I J u) = Ideal.span {q} →
      q.IsHomogeneous (2 ^ s.length * D ^ 2) → (MvPolynomial.finSuccEquiv ℚ 3 q).Monic →
      ∀ a : ℚ, a ≠ 0 → ∀ Q : MvPolynomial (Fin 4) ℤ, Q.IsHomogeneous (2 ^ s.length * D ^ 2) →
      MvPolynomial.map (Int.castRingHom ℚ) Q = MvPolynomial.C a * q →
      Irreducible (MvPolynomial.map (algebraMap ℚ (AlgebraicClosure ℚ))
        (MvPolynomial.map (Int.castRingHom ℚ) Q)) →
      (∀ m, |Q.coeff m| ≤ (A : ℤ)) →
      ∃ B : ℤ, B ≠ 0 ∧ B.natAbs ≤ T*A^N ∧
        ∀ (p : ℕ) (_hp : p.Prime), K ≤ p → ¬ (p : ℤ) ∣ B →
          (Fintype.card (PaperP1.P3CanonicalSmoothResidues.Class p Q) : ℝ) ≤ (1+η)*(p : ℝ)^2 := by
  have hd : 0 < 2 ^ k * D ^ 2 := by positivity
  obtain ⟨T, N, hT, hBudget⟩ := bounded_model_certificate (2 ^ k * D ^ 2) hd
  obtain ⟨K, hK⟩ := PaperP1.ActualAffineHypersurfacePointCount.uniform_upper_bound
    k D M (2 ^ k * D ^ 2) hD η hη
  refine ⟨K, T * (2 * 2 ^ (M*(M-1))), N + M*(M-1), by positivity, ?_⟩
  intro A hA s hlen c I J hsupport hI hJ hne hshifts hs u q hideal hq hm a ha Q hQ hmodel hgeom hcoef
  rw [← hlen] at hK hBudget
  obtain ⟨B₀, hB₀, hbound₀, hProps⟩ := hBudget A hA Q hQ hgeom hcoef q a ha hq hm hmodel
  obtain ⟨B, hB, hbound, hAvoid⟩ := PaperP1.BranchModelReductionCertificate.combine M T N A hA
    (PaperP1.SplitBranchPrimeCertificate.support I J) hsupport hshifts B₀ hB₀ hbound₀
  refine ⟨B, hB, hbound, ?_⟩
  intro p hp hlarge hnot
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hnotModel, hnotBranch⟩ := hAvoid p hnot
  have hprops := hProps p hp hnotModel
  have hroot := original_model_relation s c D hD I J hs u q hideal a Q hmodel
    (topCoefficient Q (2 ^ s.length * D ^ 2)) (ZMod p)
  have hcount := hK p hp hlarge (fun i ↦ (c i : ZMod p)) I J hsupport hI hJ hne hnotBranch
    (fieldPrimitive (ZMod p) s.length D c I J u)
    (PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q (2 ^ s.length * D ^ 2))))
    hprops.1 hprops.2.2.1 hroot (by rw [hprops.2.1]) (le_of_eq hprops.2.1) hprops.2.2.2
  have hc := PaperP1.CanonicalClassesToMonicHypersurface.cardinality_le p Q
    (topCoefficient Q (2 ^ s.length * D ^ 2))
  have hcR : (Fintype.card (PaperP1.P3CanonicalSmoothResidues.Class p Q) : ℝ) ≤
      (Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p)
        (PaperP1.MonicP3LastChart.chart (normalized (ZMod p) Q (topCoefficient Q (2 ^ s.length * D ^ 2))))) : ℝ) := by
    exact_mod_cast hc
  exact hcR.trans hcount

end PaperP1.OriginalSourceFiniteFieldBudget
