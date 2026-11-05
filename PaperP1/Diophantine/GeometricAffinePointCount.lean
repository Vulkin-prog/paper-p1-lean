module

public import PaperP1.Diophantine.FinitePrimeAffineCount
public import PaperP1.Analysis.AffineDeterminantDegreeChoice

/-! # A global affine integer point count at exponent 1/b+epsilon

The constant is uniform in coefficients and actual finite signed populations,
with an explicit height(G)^epsilon factor. The bidegrees remain fixed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricAffinePointCount

open Polynomial Finset BivariateDegrees BivariateHeight GeometricFactorSwap

theorem finite_count (a b : ℕ) (ha : 0 < a) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b → Geometric G →
      ∀ B : ℝ, 1 ≤ B → ∀ S : Finset (ℤ × ℤ),
      (∀ z ∈ S, G.evalEval z.1 z.2 = 0) →
      (∀ z ∈ S, |(z.1 : ℝ)| ≤ B) → (∀ z ∈ S, |(z.2 : ℝ)| ≤ B) →
        (S.card : ℝ) ≤ K * B ^ (1 / (b : ℝ) + ε) * (height G : ℝ) ^ ε := by
  let α : ℝ := 1 / (b : ℝ) + ε / 2
  let β : ℝ := ε / 2
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hαβ : β ≤ α := by
    have hn : (0 : ℝ) ≤ 1 / (b : ℝ) := by positivity
    dsimp only [α, β]
    linarith
  have hα : 0 ≤ α := hβ.le.trans hαβ
  obtain ⟨A, _hA, hrest⟩ := AffineDeterminantDegreeChoice.exists_auxiliary_degree b hb ε hε
  let J := b - 1
  let k := (A + 1) * (J + 1)
  let v := k * (k - 1) / 2
  have hexps : 1 ≤ v ∧ (AffineMonomialDeterminant.weightSum A J : ℝ) ≤ α * v := hrest
  obtain ⟨hv, hweight⟩ := hexps
  obtain ⟨m, hm, hAX, hAV⟩ := LocalDeterminantDegreeChoice.exists_avoidance_power
    (a + b + 1) 1 α β hβ hαβ
  let Ddet : ℝ := k.factorial
  let Dobs : ℝ := ((a : ℝ) + 1) * ((b : ℝ) + 1) * b
  let C := Ddet + Dobs + 1
  have hDdet0 : 0 ≤ Ddet := by dsimp only [Ddet]; positivity
  have hDobs0 : 0 ≤ Dobs := by dsimp only [Dobs]; positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hDdet : Ddet < C := by dsimp only [C]; linarith
  have hDobs : Dobs < C := by dsimp only [C]; linarith
  let E : ℕ := 4 * (b + 1) + 4 * (a + 1) + 8 * a * b ^ 2
  let R : ℕ := (a + b) ^ 2 * (A + J) * (m * 2 ^ m)
  let K : ℝ := E + 2 * (R : ℝ) * C
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro G hGa hGb hgeom B hB S hcurve hx hy
  have hne : G ≠ 0 := by
    intro hz
    have hd : degreeY G = 0 := by simp only [hz, degreeY, Polynomial.natDegree_zero]
    omega
  let V : ℝ := height G
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact_mod_cast GeometricBiformCoarseCount.height_pos G hne
  obtain ⟨P, hPpos, hPscale, hPupper⟩ := MonomialPrimeScale.rounded_base C B V α β
    hC hB hV hα hβ.le
  have hdet := AffineDeterminantDegreeChoice.determinant_small A J v C B V α β (P : ℝ)
    hC hDdet hB hV hv hweight hβ.le hPscale
  have hobs := MonomialPrimeScale.strict_power_domination C Dobs B V α β (P : ℝ)
    (a + b + 1) 1 m hC hDobs hB hV hm hAX hAV hPscale
  have hheight : (degreeX G + 1) * (degreeY G + 1) * degreeY G * (height G : ℝ) *
      B ^ (degreeX G + 1) * B ^ degreeY G < (P : ℝ) ^ m := by
    rw [hGa, hGb]
    calc
      _ = Dobs * B ^ (a + b + 1) * V ^ 1 := by
        have he : a + b + 1 = (a + 1) + b := by omega
        rw [he, pow_add, pow_one]
        dsimp only [Dobs, V]
        ring
      _ < _ := hobs
  have hJ : J < degreeY G := by rw [hGb]; dsimp only [J]; omega
  have hc := FinitePrimeAffineCount.bounded_count G hne hgeom
    (by rw [hGa]; exact ha) (by rw [hGb]; omega) A J hJ B hB P m hPpos hdet hheight S hcurve hx hy
  rw [hGa, hGb] at hc
  have hcNat : S.card ≤ E + R * P := by simpa only [E, R, Nat.mul_assoc] using hc
  have hcReal : (S.card : ℝ) ≤ (E : ℝ) + (R : ℝ) * P := by exact_mod_cast hcNat
  let W : ℝ := B ^ α * V ^ β
  have hW : 1 ≤ W := by
    have hBA := Real.one_le_rpow hB hα
    have hVB := Real.one_le_rpow hV hβ.le
    exact (by norm_num : (1 : ℝ) = 1 * 1).trans_le
      (mul_le_mul hBA hVB (by norm_num) (by positivity))
  have hEW : (E : ℝ) ≤ (E : ℝ) * W := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg (α := ℝ) E)
  have hRP : (R : ℝ) * P ≤ (R : ℝ) * (2 * (C * B ^ α * V ^ β)) :=
    mul_le_mul_of_nonneg_left hPupper (Nat.cast_nonneg (α := ℝ) R)
  have hcount : (S.card : ℝ) ≤ K * W := by
    calc
      _ ≤ (E : ℝ) + (R : ℝ) * P := hcReal
      _ ≤ (E : ℝ) * W + (R : ℝ) * (2 * (C * B ^ α * V ^ β)) := add_le_add hEW hRP
      _ = K * W := by dsimp only [K, W]; ring
  have hBX : B ^ α ≤ B ^ (1 / (b : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hB (by dsimp only [α]; linarith)
  have hVX : V ^ β ≤ V ^ ε := Real.rpow_le_rpow_of_exponent_le hV (by dsimp only [β]; linarith)
  calc
    (S.card : ℝ) ≤ K * W := hcount
    _ = K * B ^ α * V ^ β := by dsimp only [W]; ring
    _ ≤ _ := by gcongr

end PaperP1.GeometricAffinePointCount
