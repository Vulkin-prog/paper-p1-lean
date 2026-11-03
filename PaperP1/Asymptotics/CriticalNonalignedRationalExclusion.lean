module

public import PaperP1.Asymptotics.CriticalNonalignedAllCoverExclusion
public import PaperP1.Arithmetic.RationalCurveRadicalTransport

/-! # Rational nonaligned covers are excluded without host independence -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.CriticalNonalignedRationalExclusion

open Polynomial Finset PaperP1.SelectedProportionalPairs

theorem eventually_no_dyadic_point (C : ℝ) (E J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ (f : ℚ[X][X]) [Fact (Irreducible f)], (Bivariate.swap f).natDegree ≤ E → f.natDegree ≤ E →
      ∀ (K : Type u) [Field K] [Algebra (AffineCurveFunctionField.FunctionField f) K]
        [Module.Finite (AffineCurveFunctionField.FunctionField f) K],
        Module.finrank (AffineCurveFunctionField.FunctionField f) K ≤ E →
      ∀ (ι : Type v) [Fintype ι] [DecidableEq ι], 4 * (E + 1) ^ 2 ≤ Fintype.card ι →
      ∀ (a : ℕ), 0 < a → ∀ (d : ι → ℤ), (∀ ν, d ν ≠ 0) →
      ∀ (I : ι → Finset ℤ) (j : ι → ℤ),
        (Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) → Function.Injective j →
        (∀ ν, (I ν).card = a) → (∀ ν, ∀ z ∈ I ν, z.natAbs ≤ B) → (∀ ν, (j ν).natAbs ≤ B) →
      ∀ (r : ι → K),
        (∀ ν, r ν ^ 2 = algebraMap (AffineCurveFunctionField.FunctionField f) K
          (RationalCurveRadicalTransport.value f d I (fun μ ↦ {j μ}) ν)) →
      ∀ S T : Finset ℤ, (∀ ν, I ν ⊆ S) → (∀ ν, j ν ∈ T) →
      ∀ X Y : ℤ, (N : ℤ) ≤ X → (N : ℤ) ≤ Y → Y.natAbs ≤ 2 * N → f.evalEval (X : ℚ) (Y : ℚ) = 0 →
        (∀ z ∈ S, 0 < X + z) → (∀ z ∈ T, 0 < Y + z) →
        ¬ AffineGridAlignment.Aligned B X Y →
        False := by
  obtain ⟨N₀, hN₀⟩ := CriticalNonalignedAllCoverExclusion.eventually_no_dyadic_point.{u,v} C E J
  refine ⟨N₀, ?_⟩
  intro N hN L B hcrit hB hBL f _ hX hY K _ _ _ hrank ι _ _ hlarge a ha d hd I j hI hj hcard hiB hjB r hr S T hiS hjT X Y hXN hYNlower hYN hpoint hposS hposT hnonaligned
  obtain ⟨P, hP, hass, hx, hy, hpoints⟩ := IntegerCurveLift.exists_integer_model f Fact.out
  let : Fact (Irreducible P) := ⟨hP⟩
  let e := IntegerCurveFieldEquiv.equiv P f hass
  let := FieldEquivScalarTransport.algebra (L := K) e
  let := FieldEquivScalarTransport.finite (L := K) e
  have hdegree : Module.finrank (CurveFunctionField.FunctionField P) K ≤ E := by
    rw [FieldEquivScalarTransport.finrank_eq e]
    exact hrank
  have hroots := RationalCurveRadicalTransport.roots P f hass d I (fun μ ↦ {j μ}) r hr
  exact hN₀ N hN L B hcrit hB hBL P (hx.trans hX) (hy.trans hY) K hdegree ι hlarge a ha d hd I j hI hj
    hcard hiB hjB r hroots S T hiS hjT X Y hXN hYNlower hYN ((hpoints X Y).mpr hpoint) hposS hposT hnonaligned

end PaperP1.CriticalNonalignedRationalExclusion
