module

public import PaperP1.Algebra.CurveRationalSquareDescent
public import PaperP1.Asymptotics.CriticalRationalSquareGraphExclusion

/-! # Actual odd-degree covers of a bounded rational plane graph have no large admissible integral hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v w

namespace PaperP1.CriticalCurveRationalOddExclusion

open Polynomial Finset PaperP1.AffineCurveFunctionField PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (C₀ : F[X][X]) [Fact (Irreducible C₀)],
        0 < C₀.natDegree → ∀ p q : F[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree ≤ E →
          aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q →
      ∀ (K : Type w) [Field K] [Algebra (FunctionField C₀) K], Odd (Module.finrank (FunctionField C₀) K) →
      ∀ (ι : Type v) [DecidableEq ι] (a : ℕ), 0 < a →
      ∀ (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F) (r : ι → K),
        3 * E + 1 ≤ A.card → (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        (∀ ν ∈ A, c ν ≠ 0) →
        (∀ ν ∈ A, r ν ^ 2 = algebraMap (FunctionField C₀) K
          (specialize C₀ (ScaledSplitWordSquares.scaledPolynomial (c ν) (I ν) {j ν}))) →
      ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
        Polynomial.aevalAeval (X : F) (Y : F) C₀ = 0 →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        EvenIndependentValues.Independent (values X S) →
        Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
        False := by
  obtain ⟨N₀, hN₀⟩ := CriticalRationalSquareGraphExclusion.eventually_no_dyadic_point.{u,v} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ C₀ _ hdegree p q hq hcop hdeg hgraph K _ _ hodd ι _ a ha A I j c r hA hdisj hcard hiB hjB hc hr S T hiS hjT X Y hXN hYN hCpoint hposS hposT hind hdirect
  have hsq (ν) (hν : ν ∈ A) : IsSquare (RationalGraphSquareRoots.value (c ν) (j ν : F)
      (FormalWordPolynomials.linearOver F (I ν)) p q) :=
    CurveRationalSquareDescent.value_isSquare C₀ hdegree p q hq hgraph hodd (c ν) (I ν) (j ν) (r ν) (hr ν hν)
  have hpoint := (AffineCurveGraphPresentation.point_iff_graph C₀ p q hq hcop hgraph (X : F) (Y : F)).mp hCpoint
  exact hN₀ N hN L B hcrit hB hBL F ι a ha A I j c hA hdisj hcard hiB hjB hc p q hq hcop hdeg hsq
    S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect

theorem eventually_even_degree (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (C₀ : F[X][X]) [Fact (Irreducible C₀)],
        0 < C₀.natDegree → ∀ p q : F[X], q ≠ 0 → IsCoprime p q → max p.natDegree q.natDegree ≤ E →
          aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q →
      ∀ (K : Type w) [Field K] [Algebra (FunctionField C₀) K] [Module.Finite (FunctionField C₀) K],
      ∀ (ι : Type v) [DecidableEq ι] (a : ℕ), 0 < a →
      ∀ (A : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (c : ι → F) (r : ι → K),
        3 * E + 1 ≤ A.card → (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        (∀ ν ∈ A, c ν ≠ 0) →
        (∀ ν ∈ A, r ν ^ 2 = algebraMap (FunctionField C₀) K
          (specialize C₀ (ScaledSplitWordSquares.scaledPolynomial (c ν) (I ν) {j ν}))) →
      ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
        Polynomial.aevalAeval (X : F) (Y : F) C₀ = 0 →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        EvenIndependentValues.Independent (values X S) →
        Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
        Even (Module.finrank (FunctionField C₀) K) := by
  obtain ⟨N₀, hN₀⟩ := eventually_no_dyadic_point.{u,v,w} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ C₀ _ hdegree p q hq hcop hdeg hgraph K _ _ _ ι _ a ha A I j c r hA hdisj hcard hiB hjB hc hr S T hiS hjT X Y hXN hYN hCpoint hposS hposT hind hdirect
  apply Nat.not_odd_iff_even.mp
  intro hodd
  exact hN₀ N hN L B hcrit hB hBL F C₀ hdegree p q hq hcop hdeg hgraph K hodd ι a ha A I j c r
    hA hdisj hcard hiB hjB hc hr S T hiS hjT X Y hXN hYN hCpoint hposS hposT hind hdirect

end PaperP1.CriticalCurveRationalOddExclusion
