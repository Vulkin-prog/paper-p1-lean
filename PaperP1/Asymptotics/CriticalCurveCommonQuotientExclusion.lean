module

public import PaperP1.Diophantine.CurveCommonQuotientBound
public import PaperP1.Asymptotics.CriticalCommonQuotientExclusion

/-! # A single uniform scale excludes actual low-curve points after the common-quotient step -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.CriticalCurveCommonQuotientExclusion

open Polynomial Finset PaperP1.AffineCurveFunctionField PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (a J : ℕ) (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (F : Type u) [Field F] [CharZero F] (C₀ : F[X][X]) [Fact (Irreducible C₀)],
        0 < C₀.natDegree → ∀ (ι : Type v) [DecidableEq ι],
      ∀ (A bad : Finset ι) (I : ι → Finset ℤ) (j : ι → ℤ) (E e : ℕ),
        e ≤ E → 4 * (E + 1) ^ 2 ≤ A.card → bad.card ≤ 2 * e ^ 2 →
        (A : Set ι).PairwiseDisjoint I → (∀ ν ∈ A, (I ν).card = a) →
        (∀ ν ∈ A, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν ∈ A, (j ν).natAbs ≤ B) →
        ∀ (b : ι → F), (∀ ν ∈ A \ bad, b ν ≠ 0) → ∀ t : FunctionField C₀,
          (∀ ν ∈ A \ bad,
            algebraMap F (FunctionField C₀) (b ν) * aeval (firstCoordinate C₀) (FormalWordPolynomials.linearOver F (I ν)) =
              t * (secondCoordinate C₀ + (j ν : FunctionField C₀))) →
        ∀ S T : Finset ℤ, (∀ ν ∈ A, I ν ⊆ S) → (∀ ν ∈ A, j ν ∈ T) →
        ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N →
          Polynomial.aevalAeval (X : F) (Y : F) C₀ = 0 →
          (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
          EvenIndependentValues.Independent (values X S) →
          Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
          False := by
  obtain ⟨N₀, hN₀⟩ := CriticalCommonQuotientExclusion.eventually_no_dyadic_point.{u,u,v} C a J ha
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL F _ _ C₀ _ hdegree ι _ A bad I j E e he hA hbad hdisj hcard hiB hjB b hb t hcommon S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect
  exact hN₀ N hN L B hcrit hB hBL F (FunctionField C₀) ι A bad I j E e he hA hbad hdisj hcard hiB hjB b hb
    (firstCoordinate C₀) (secondCoordinate C₀) t (first_transcendental C₀ hdegree) hcommon
    S T hiS hjT X Y hXN hYN (point_kernel_le C₀ (X : F) (Y : F) hpoint) hposS hposT hind hdirect

end PaperP1.CriticalCurveCommonQuotientExclusion
