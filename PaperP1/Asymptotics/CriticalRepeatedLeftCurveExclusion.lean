module

public import PaperP1.Diophantine.CurveCoverRepeatedLeftBound
public import PaperP1.Asymptotics.BoundedDegreeGridGraphExclusion

/-! # A uniform repeated-left cover exclusion without host independence -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.CriticalRepeatedLeftCurveExclusion

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)],
        0 < degreeX C₀ → 0 < degreeY C₀ → degreeX C₀ ≤ E → degreeY C₀ ≤ E →
      ∀ (K : Type u) [Field K] [Algebra (FunctionField C₀) K] [Module.Finite (FunctionField C₀) K],
        Module.finrank (FunctionField C₀) K ≤ E →
      ∀ (ι : Type v) [Fintype ι] [DecidableEq ι], 4 * (E + 1) ^ 2 ≤ Fintype.card ι →
      ∀ (a : ℕ), 2 ≤ a → ∀ (d : ι → ℤ), (∀ ν, d ν ≠ 0) →
      ∀ (I : ι → Finset ℤ) (j : ι → ℤ),
        (Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) → Function.Injective j →
        (∀ ν, (I ν).card = a) → (∀ ν, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν, (j ν).natAbs ≤ B) →
      ∀ (r : ι → K),
        (∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) K
          (ScaledCurveEquationClasses.value C₀ d I (fun μ ↦ {j μ}) ν)) →
      ∀ S T : Finset ℤ, (∀ ν, I ν ⊆ S) → (∀ ν, j ν ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → Y.natAbs ≤ 2 * N → C₀.evalEval X Y = 0 →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        False := by
  obtain ⟨N₀, hN₀⟩ := BoundedDegreeGridGraphExclusion.cutoff_lt_scale C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL C₀ _ hx hy hX hY K _ _ _ hrank ι _ _ hlarge a ha d hd I j hI hj hcard hiB hjB r hr S T hiS hjT X Y hXN hYN hpoint hposS hposT
  have hXNabs : N ≤ X.natAbs := by
    have hz : (N : ℤ) ≤ (X.natAbs : ℤ) := hXN.trans Int.le_natAbs
    exact_mod_cast hz
  obtain ⟨n, hn, hnE, hbound⟩ := CurveCoverRepeatedLeftBound.integral_point C₀ hx hy d hd I j a B E ha hB
    hI hj hcard hiB hjB hX hY hrank hlarge r hr X Y
    (hYN.trans (Nat.mul_le_mul_left 2 hXNabs)) hpoint (fun ν ↦ hposT (j ν) (hjT ν))
  exact Nat.not_lt_of_ge hXNabs (hbound.trans_lt (hN₀ N hN L B hcrit hB hBL n hn hnE))

end PaperP1.CriticalRepeatedLeftCurveExclusion
