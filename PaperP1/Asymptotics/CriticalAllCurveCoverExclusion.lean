module

public import PaperP1.Asymptotics.CriticalCurveCoverExclusion
public import PaperP1.Arithmetic.ConstantCurveCoverDegree

/-! # One scale excludes all bounded-degree actual integer plane radical covers, including constant-coordinate images -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.CriticalAllCurveCoverExclusion

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)], degreeX C₀ ≤ E → degreeY C₀ ≤ E →
      ∀ (K : Type u) [Field K] [Algebra (FunctionField C₀) K] [Module.Finite (FunctionField C₀) K],
        Module.finrank (FunctionField C₀) K ≤ E →
      ∀ (ι : Type v) [Fintype ι] [DecidableEq ι], 4 * (E + 1) ^ 2 ≤ Fintype.card ι →
      ∀ (a : ℕ), 0 < a → ∀ (d : ι → ℤ), (∀ ν, d ν ≠ 0) →
      ∀ (I : ι → Finset ℤ) (j : ι → ℤ),
        (Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) → Function.Injective j →
        (∀ ν, (I ν).card = a) → (∀ ν, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν, (j ν).natAbs ≤ B) →
      ∀ (r : ι → K),
        (∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) K
          (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν)) →
      ∀ S T : Finset ℤ, (∀ ν, I ν ⊆ S) → (∀ ν, j ν ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N → C₀.evalEval X Y = 0 →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        EvenIndependentValues.Independent (values X S) →
        Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T)) →
        False := by
  obtain ⟨N₀, hN₀⟩ := CriticalCurveCoverExclusion.eventually_no_dyadic_point.{u,v} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL C₀ _ hX hY K _ _ _ hrank ι _ _ hlarge a ha d hd I j hI hj hcard hiB hjB r hr S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect
  have hEcard : E ≤ Fintype.card ι := by nlinarith
  have hne (ν : ι) : (I ν).Nonempty := Finset.card_pos.mp (by rw [hcard ν]; exact ha)
  obtain ⟨hx, hy⟩ := ConstantCurveCoverDegree.partial_degrees_pos C₀ d hd I j X Y hpoint
    (fun ν z hz ↦ hposS z (hiS ν hz)) (fun ν ↦ hposT (j ν) (hjT ν)) hne hI hj r hr E hrank hEcard
  exact hN₀ N hN L B hcrit hB hBL C₀ hx hy hX hY K hrank ι hlarge a ha d hd I j hI hj
    hcard hiB hjB r hr S T hiS hjT X Y hXN hYN hpoint hposS hposT hind hdirect

end PaperP1.CriticalAllCurveCoverExclusion
