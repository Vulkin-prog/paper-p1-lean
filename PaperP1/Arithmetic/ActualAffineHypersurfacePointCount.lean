module

public import PaperP1.Algebra.AffineProjectionHypersurfacePoints
public import PaperP1.Arithmetic.ActualAffineProjectionPointCount

/-! # Uniform bounds for every literal affine hypersurface solution from the actual full-degree source model

The exact hypersurface/image point equivalence is proved internally. The
cutoff precedes all primes, source coefficients, bounded branch supports,
source elements and polynomials. Original integer-model normalization and
effective prime/cover assembly are separate remaining obligations.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualAffineHypersurfacePointCount
open Polynomial PaperP1.LocalizedAffineQuadraticSource PaperP1.AffinePowerParameterFractionField
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarTower
open PaperP1.SplitRadicalCoordinateAlgebra

theorem cardinality_le (p : ℕ) [Fact p.Prime] (k D : ℕ) (hD : 0 < D)
    (c : Fin k → ZMod p) (I J : Fin k → Finset ℤ)
    (y : CoordinateAlgebra (List.finRange k) c I J)
    (P : (Parameters (ZMod p))[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hy : letI := sourceAlgebra (ZMod p) D (radicands (List.finRange k) c I J); Polynomial.aeval y P = 0)
    (hfull : 2 ^ k * D ^ 2 ≤ P.natDegree) (d : ℕ) (hdegree : P.natDegree ≤ d) (hlt : d < p)
    (hcoef : ∀ i, (P.coeff i).totalDegree ≤ d) :
    Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p) P) ≤
      (PaperP1.SplitRadicalFiniteFieldPointCount.points c I J).card + 2*d^3*p := by
  have hh := PaperP1.ActualAffineProjectionPointCount.cardinality_le p k D hD c I J y P
    hmonic hP hy hfull d hdegree hlt hcoef
  rw [PaperP1.AffineProjectionHypersurfacePoints.point_cardinality (ZMod p) D hD
    (radicands (List.finRange k) c I J) P hmonic hP y hy] at hh
  exact hh

theorem uniform_upper_bound (k D M d : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (c : Fin k → ZMod p) (I J : Fin k → Finset ℤ),
      (PaperP1.SplitBranchPrimeCertificate.support I J).card ≤ M →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ PaperP1.BranchShiftReductionCertificate.certificate
        (PaperP1.SplitBranchPrimeCertificate.support I J) →
      ∀ (y : CoordinateAlgebra (List.finRange k) c I J) (P : (Parameters (ZMod p))[X]),
      P.Monic → Irreducible P →
      (letI := sourceAlgebra (ZMod p) D (radicands (List.finRange k) c I J); Polynomial.aeval y P = 0) →
      2 ^ k * D ^ 2 ≤ P.natDegree → P.natDegree ≤ d →
      (∀ i, (P.coeff i).totalDegree ≤ d) →
      ((Nat.card (PaperP1.AffineProjectionHypersurfacePoints.Solution (ZMod p) P) : ℕ) : ℝ) ≤
        (1+η)*(p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := PaperP1.ActualAffineProjectionPointCount.uniform_upper_bound k D M d hD η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro c I J hsupport hI hJ hne hnot y P hmonic hP hy hfull hdegree hcoef
  have hh := hK p hp hlarge c I J hsupport hI hJ hne hnot y P hmonic hP hy hfull hdegree hcoef
  rw [PaperP1.AffineProjectionHypersurfacePoints.point_cardinality (ZMod p) D hD
    (radicands (List.finRange k) c I J) P hmonic hP y hy] at hh
  exact hh

end PaperP1.ActualAffineHypersurfacePointCount
