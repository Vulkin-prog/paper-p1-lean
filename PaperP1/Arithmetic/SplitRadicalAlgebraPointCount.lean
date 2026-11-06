module

public import PaperP1.Algebra.BivariateQuadraticTowerPoints
public import PaperP1.Arithmetic.SplitRadicalUniformPointEstimate

/-! # Actual algebra points of the split-radical source have the proved uniform field-point count

The point equivalence uses the literal scaled split polynomials, not an
assumed matching cardinality. Thresholds precede all primes and coefficients.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SplitRadicalAlgebraPointCount
open Polynomial Finset PaperP1.FiniteQuadraticTower
open PaperP1.SplitRadicalFiniteFieldPointCount PaperP1.SplitBranchPrimeCertificate
open PaperP1.BranchShiftReductionCertificate
open scoped Classical
attribute [local instance] PaperP1.BivariateQuadraticTowerPoints.scalarAlgebra

variable {F : Type*} [Field F] [Fintype F]
  (s : List F[X][X]) (c : Fin s.length → F) (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = PaperP1.ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i))

def concreteEquiv : PaperP1.BivariateQuadraticTowerPoints.Point s ≃ {v // v ∈ points c I J} where
  toFun v := ⟨v.val, (mem_points_iff c I J v.val).mpr (fun i ↦ by rw [← hs i]; exact v.property i)⟩
  invFun v := ⟨v.val, fun i ↦ by
    rw [hs i]
    exact (mem_points_iff c I J v.val).mp v.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl

def pointsEquiv : (Tower F[X][X] s →ₐ[F] F) ≃ {v // v ∈ points c I J} :=
  (PaperP1.BivariateQuadraticTowerPoints.pointsEquiv s).trans (concreteEquiv s c I J hs)

include hs in
theorem cardinality : Nat.card (Tower F[X][X] s →ₐ[F] F) = (points c I J).card :=
  (Nat.card_congr (pointsEquiv s c I J hs)).trans (Nat.card_eq_finsetCard (points c I J))

theorem uniform_absolute (k D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (s : List (ZMod p)[X][X]), s.length = k →
      ∀ (c : Fin s.length → ZMod p) (I J : Fin s.length → Finset ℤ),
      (∀ i, s.get i = PaperP1.ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i)) →
      (support I J).card ≤ D →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ certificate (support I J) →
        |((Nat.card (Tower (ZMod p)[X][X] s →ₐ[ZMod p] ZMod p) : ℕ) : ℝ) - (p : ℝ)^2| ≤
          η * (p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := PaperP1.SplitRadicalUniformPointEstimate.uniform_absolute (ι := Fin k) D η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hs hD hI hJ hne hnot
  subst k
  rw [cardinality s c I J hs]
  exact hK I J hD hI hJ hne p hp hlarge hnot c

theorem uniform_upper_bound (k D : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ (p : ℕ) (hp : p.Prime), K ≤ p →
      letI : Fact p.Prime := ⟨hp⟩
      ∀ (s : List (ZMod p)[X][X]), s.length = k →
      ∀ (c : Fin s.length → ZMod p) (I J : Fin s.length → Finset ℤ),
      (∀ i, s.get i = PaperP1.ScaledSplitWordSquares.scaledPolynomial (c i) (I i) (J i)) →
      (support I J).card ≤ D →
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ i, (I i).Nonempty ∨ (J i).Nonempty) →
      ¬ (p : ℤ) ∣ certificate (support I J) →
        ((Nat.card (Tower (ZMod p)[X][X] s →ₐ[ZMod p] ZMod p) : ℕ) : ℝ) ≤
          (1+η) * (p : ℝ)^2 := by
  obtain ⟨K, hK⟩ := uniform_absolute k D η hη
  refine ⟨K, ?_⟩
  intro p hp hlarge
  let : Fact p.Prime := ⟨hp⟩
  intro s hlen c I J hs hD hI hJ hne hnot
  have he := hK p hp hlarge s hlen c I J hs hD hI hJ hne hnot
  have hl := le_abs_self (((Nat.card (Tower (ZMod p)[X][X] s →ₐ[ZMod p] ZMod p) : ℕ) : ℝ) - (p : ℝ)^2)
  nlinarith only [he, hl]

end PaperP1.SplitRadicalAlgebraPointCount
