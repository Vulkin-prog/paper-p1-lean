module

public import PaperP1.Diophantine.FinitePrimeBiformCount
public import PaperP1.Diophantine.HeathBrownHigherDegreeBiformInput
public import PaperP1.Analysis.LocalDeterminantDegreeChoice

/-! # The sharp geometric biform count on the full original signed primitive population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricBiformPointCount

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.BivariateHeight

theorem higher_input : HeathBrownHigherDegreeBiformInput.Input := by
  intro a b ha hb ε hε
  let α : ℝ := 2 / (b : ℝ) + ε / 2
  let β : ℝ := ε / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hαβ : β ≤ α := by
    have hd : (0 : ℝ) ≤ 2 / (b : ℝ) := by positivity
    dsimp [α, β]
    linarith
  have hα : 0 ≤ α := hβ.le.trans hαβ
  obtain ⟨H, hH, hrest⟩ := LocalDeterminantDegreeChoice.exists_auxiliary_degree a b hb ε hε
  let J := b - 1
  let k := (H + 1) * (J + 1)
  let N := k * (k - 1) / 2
  have hexps : 1 ≤ N ∧ (((H * k + a * J * k : ℕ) : ℝ) ≤ α * N) ∧
      (((J * k : ℕ) : ℝ) ≤ β * N) := hrest
  obtain ⟨hN, hXexp, hYexp⟩ := hexps
  obtain ⟨m, hm, hAX, hAV⟩ := LocalDeterminantDegreeChoice.exists_avoidance_power
    (a * b + a + 1) (b + 1) α β hβ hαβ
  let Ddet : ℝ := (k.factorial : ℝ) * ((a : ℝ) + 1) ^ (J * k)
  let Dobs : ℝ := ((a : ℝ) + 1) * ((b : ℝ) + 1) * b * ((a : ℝ) + 1) ^ b
  let C := Ddet + Dobs + 1
  have hDdet0 : 0 ≤ Ddet := by dsimp [Ddet]; positivity
  have hDobs0 : 0 ≤ Dobs := by dsimp [Dobs]; positivity
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hDdet : Ddet < C := by dsimp [C]; linarith
  have hDobs : Dobs < C := by dsimp [C]; linarith
  let E : ℕ := 8 * (a + 1) * (b + 1) + 4 * (b + 1) + 4 * (a + 1) + 8 * a * b ^ 2
  let B : ℕ := 4 * (a + b) ^ 2 * (H + J) * (m * 2 ^ m)
  let K : ℝ := E + 2 * (B : ℝ) * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro G hGa hGb hgeom L hL S hprim hcurve hbox
  have hne : G ≠ 0 := by
    intro hz
    have hd : degreeY G = 0 := by simp only [hz, degreeY, Polynomial.natDegree_zero]
    omega
  let V : ℝ := height G
  have hV : 1 ≤ V := by
    dsimp only [V]
    exact_mod_cast GeometricBiformCoarseCount.height_pos G hne
  obtain ⟨P, hPpos, hPscale, hPupper⟩ := MonomialPrimeScale.rounded_base C L V α β hC hL hV hα hβ.le
  have hdet := MonomialPrimeScale.determinant_small a H J k N C L V α β (P : ℝ)
    hC hDdet hL hV hN hXexp hYexp hPscale
  have hheight := MonomialPrimeScale.obstruction_small a b m C L V α β (P : ℝ)
    hC hDobs hL hV hm hAX hAV hPscale
  have hJ : J < degreeY G := by rw [hGb]; dsimp [J]; omega
  have hc := FinitePrimeBiformCount.unrestricted_second_pair_count G hne hgeom
    (by rw [hGa]; exact ha) (by rw [hGb]; omega) H J hJ L hL P m hPpos
    (by simpa only [hGa, V, k, N, Nat.cast_add, Nat.cast_one] using hdet)
    (by simpa only [hGa, hGb, V, Nat.cast_add, Nat.cast_one] using hheight)
    S hprim hcurve hbox
  rw [hGa, hGb] at hc
  have hcNat : S.card ≤ E + B * P := by
    simpa only [E, B, Nat.mul_assoc] using hc
  have hcReal : (S.card : ℝ) ≤ (E : ℝ) + (B : ℝ) * P := by exact_mod_cast hcNat
  let W : ℝ := L ^ α * V ^ β
  have hW : 1 ≤ W := by
    have hLA := Real.one_le_rpow hL hα
    have hVB := Real.one_le_rpow hV hβ.le
    exact (by norm_num : (1 : ℝ) = 1 * 1).trans_le
      (mul_le_mul hLA hVB (by norm_num) (by positivity))
  have hEW : (E : ℝ) ≤ (E : ℝ) * W := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg (α := ℝ) E)
  have hBP : (B : ℝ) * P ≤ (B : ℝ) * (2 * (C * L ^ α * V ^ β)) :=
    mul_le_mul_of_nonneg_left hPupper (Nat.cast_nonneg (α := ℝ) B)
  have hcount : (S.card : ℝ) ≤ K * W := by
    calc
      _ ≤ (E : ℝ) + (B : ℝ) * P := hcReal
      _ ≤ (E : ℝ) * W + (B : ℝ) * (2 * (C * L ^ α * V ^ β)) := add_le_add hEW hBP
      _ = K * W := by dsimp only [K, W]; ring
  have hLX : L ^ α ≤ L ^ (2 / (b : ℝ) + ε) :=
    Real.rpow_le_rpow_of_exponent_le hL (by dsimp [α]; linarith)
  have hVX : V ^ β ≤ V ^ ε := Real.rpow_le_rpow_of_exponent_le hV (by dsimp [β]; linarith)
  calc
    (S.card : ℝ) ≤ K * W := hcount
    _ = K * L ^ α * V ^ β := by dsimp only [W]; ring
    _ ≤ K * L ^ (2 / (b : ℝ) + ε) * V ^ ε := by gcongr

theorem full_input : HeathBrownBiformInput.Input :=
  HeathBrownHigherDegreeBiformInput.full_input higher_input

end PaperP1.GeometricBiformPointCount
