module

public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Algebra.NormalizedQuotientPoints
public import PaperP1.Algebra.ZModPointEvaluations
public import PaperP1.Arithmetic.SplitRadicalCanonicalPointCount

/-! # Literal normalized source-Veronese points have the full unconditional relative count

The quotient by Z^D-1, the actual graded chart and the affine equations give
an exact point equivalence. No extra factor D enters the point count.
The branch support cap follows from the actual equation degrees.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open scoped Classical
namespace PaperP1.SplitRadicalNormalizedPointCount
open Polynomial Finset PaperP1.FiniteQuadraticTower
open PaperP1.SplitRadicalFiniteFieldPointCount PaperP1.SplitBranchPrimeCertificate
open PaperP1.BranchShiftReductionCertificate
open PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalVeronese
open PaperP1.SourceVeroneseGrading PaperP1.VeroneseCoordinateCharts
open PaperP1.SplitRadicalCoordinateAlgebra
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra

variable (p : ℕ) [Fact p.Prime]
  (s : List (PolynomialRing (ZMod p))) (c : Fin s.length → ZMod p) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2*D)
  (hs : ∀ i, s.get i = radicand (c i) (2*D-((I i).card+(J i).card)) (I i) (J i)) (hD : 0 < D)

def normalizedEquiv :
    {φ : veronese c D I J →+* ZMod p // φ (sourceCoordinate c D I J hdeg 2) = 1} ≃
      (CoordinateAlgebra (List.finRange s.length) c I J →ₐ[ZMod p] ZMod p) := by
  let := PaperP1.HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let := sourceGrading c D I J hdeg hD
  let e := (PaperP1.GradedDehomogenizationQuotient.equiv (sourcePiece c D I J)
    (sourceCoordinate_mem c D I J hdeg 2)).trans (PaperP1.SourceAffineChart.affineEquiv s c D I J hdeg hs hD)
  exact (PaperP1.NormalizedQuotientPoints.quotientEquiv (sourceCoordinate c D I J hdeg 2)).trans
    ((PaperP1.NormalizedQuotientPoints.ringEquivPoints e).trans (PaperP1.ZModPointEvaluations.ringHomEquiv p (CoordinateAlgebra (List.finRange s.length) c I J)))

def normalizedPointEquiv :
    {φ : veronese c D I J →+* ZMod p // φ (sourceCoordinate c D I J hdeg 2) = 1} ≃
      {v // v ∈ points c I J} :=
  (normalizedEquiv p s c D I J hdeg hs hD).trans
    (PaperP1.SplitRadicalCanonicalPointCount.pointsEquiv s.length c I J)

include hs hD in
theorem normalized_finite :
    Finite {φ : veronese c D I J →+* ZMod p // φ (sourceCoordinate c D I J hdeg 2) = 1} :=
  Finite.of_equiv {v // v ∈ points c I J} (normalizedPointEquiv p s c D I J hdeg hs hD).symm

include hs hD in
theorem cardinality :
    Nat.card {φ : veronese c D I J →+* ZMod p // φ (sourceCoordinate c D I J hdeg 2) = 1} =
      (points c I J).card :=
  (Nat.card_congr (normalizedPointEquiv p s c D I J hdeg hs hD)).trans
    (Nat.card_eq_finsetCard (points c I J))

theorem support_card_le (k D : ℕ) (I J : Fin k → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2*D) :
    (support I J).card ≤ 2*D*k := by
  calc
    (support I J).card ≤ (univ.biUnion I).card + (univ.biUnion J).card := card_union_le _ _
    _ ≤ (∑ i : Fin k, (I i).card) + ∑ i : Fin k, (J i).card :=
      Nat.add_le_add card_biUnion_le card_biUnion_le
    _ = ∑ i : Fin k, ((I i).card + (J i).card) := sum_add_distrib.symm
    _ ≤ ∑ _i : Fin k, 2*D := sum_le_sum (fun i _ ↦ hdeg i)
    _ = 2*D*k := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

theorem uniform_absolute (k D : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (s : List (PolynomialRing (ZMod p))), s.length = k →
      ∀ (c : Fin s.length → ZMod p) (I J : Fin s.length → Finset ℤ)
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2*D),
      (∀ i, s.get i = radicand (c i) (2*D-((I i).card+(J i).card)) (I i) (J i)) →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ certificate (support I J) →
        |((Nat.card {φ : veronese c D I J →+* ZMod p //
          φ (sourceCoordinate c D I J hdeg 2) = 1} : ℕ) : ℝ) - (p : ℝ)^2| ≤ η * (p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := PaperP1.SplitRadicalUniformPointEstimate.uniform_absolute (ι := Fin k) (2*D*k) η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hdeg hs hI hJ hne hnot
  subst k
  rw [cardinality p s c D I J hdeg hs hD]
  exact hK I J (support_card_le s.length D I J hdeg) hI hJ hne p hp hlarge hnot c

theorem uniform_upper_bound (k D : ℕ) (hD : 0 < D) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (s : List (PolynomialRing (ZMod p))), s.length = k →
      ∀ (c : Fin s.length → ZMod p) (I J : Fin s.length → Finset ℤ)
        (hdeg : ∀ i, (I i).card + (J i).card ≤ 2*D),
      (∀ i, s.get i = radicand (c i) (2*D-((I i).card+(J i).card)) (I i) (J i)) →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ certificate (support I J) →
        ((Nat.card {φ : veronese c D I J →+* ZMod p //
          φ (sourceCoordinate c D I J hdeg 2) = 1} : ℕ) : ℝ) ≤ (1+η) * (p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := uniform_absolute k D hD η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hdeg hs hI hJ hne hnot
  have he := hK p hp hlarge s hlen c I J hdeg hs hI hJ hne hnot
  have hl := le_abs_self (((Nat.card {φ : veronese c D I J →+* ZMod p //
    φ (sourceCoordinate c D I J hdeg 2) = 1} : ℕ) : ℝ) - (p : ℝ)^2)
  nlinarith only [he, hl]

end PaperP1.SplitRadicalNormalizedPointCount
