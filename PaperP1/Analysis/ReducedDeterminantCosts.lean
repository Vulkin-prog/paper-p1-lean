module

public import PaperP1.Analysis.ReducedDeterminantShape

/-! # Compare both complete determinant costs at the reduced and original scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedDeterminantCosts

open PaperP1.DeterminantSourceBox PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter
open PaperP1.DeterminantLogScale PaperP1.DeterminantShapeStability

theorem pair_cost_inflation (D E D' E' F F' K R : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (_hD' : 0 ≤ D') (hE' : 0 ≤ E') (_hF : 0 ≤ F) (hF' : 0 ≤ F')
    (hK : 0 ≤ K) (hR : 1 ≤ R) (hd : D' ≤ K * D) (he : E' ≤ K * E) (hf : F' ≤ R ^ 2 * F) :
    Real.sqrt (D' * E' * F') + D' + E' ≤ K * R * (Real.sqrt (D * E * F) + D + E) := by
  have hprod : D' * E' ≤ K ^ 2 * (D * E) := by
    have hh := mul_le_mul hd he hE' (mul_nonneg hK hD)
    nlinarith only [hh]
  have htotal : D' * E' * F' ≤ (K * R) ^ 2 * (D * E * F) := by
    calc
      _ ≤ (K ^ 2 * (D * E)) * (R ^ 2 * F) :=
        mul_le_mul hprod hf hF' (by positivity)
      _ = _ := by ring
  have hKR : 0 ≤ K * R := mul_nonneg hK (by linarith)
  have haxesD := mul_nonneg (mul_nonneg hK hD) (sub_nonneg.mpr hR)
  have haxesE := mul_nonneg (mul_nonneg hK hE) (sub_nonneg.mpr hR)
  calc
    _ ≤ Real.sqrt ((K * R) ^ 2 * (D * E * F)) + K * D + K * E := by
      exact add_le_add (add_le_add (Real.sqrt_le_sqrt htotal) hd) he
    _ = K * R * Real.sqrt (D * E * F) + K * D + K * E := by
      rw [Real.sqrt_mul (sq_nonneg (K * R)), Real.sqrt_sq hKR]
    _ ≤ _ := by nlinarith only [haxesD, haxesE]

theorem uniform_cost_comparison (C K A ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      ∀ ρ δ : ℝ, ∀ X : Box N ρ C δ, ∀ g q : ℕ, 0 < g → 0 < q → g ^ 2 * q ≤ h →
      let N' := parameter N (g ^ 2 * q)
      let D' := enlarged X.D g
      let E' := enlarged X.E g
      let U' := enlarged X.U q
      let V' := enlarged X.V q
      let F' := Real.exp (logShape N' D' E' U' V')
      let F := Real.exp (logShape N X.D X.E X.U X.V)
      Real.sqrt (D' * E' * F') + D' + E' ≤ (N : ℝ) ^ ε * (Real.sqrt (X.D * X.E * F) + X.D + X.E) ∧
        Real.sqrt (U' * V' * F') + U' + V' ≤ (N : ℝ) ^ ε * (Real.sqrt (X.U * X.V * F) + X.U + X.V) := by
  obtain ⟨Ns, hs⟩ := ReducedDeterminantShape.uniform_exp_comparison C K A (2 * ε) hC (by positivity)
  refine ⟨max 1 Ns, ?_⟩
  intro N hN h hh hshift ρ δ X g q hg hq hscale
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hn₁ hε.le
  have hpower : (N : ℝ) ^ (2 * ε) = ((N : ℝ) ^ ε) ^ 2 := by
    rw [mul_comm (2 : ℝ) ε, Real.rpow_mul (Nat.cast_nonneg N), Real.rpow_two]
  have hf := hs N (by omega) h hh hshift ρ δ X g q hg hq hscale
  rw [hpower] at hf
  constructor
  · have hc := pair_cost_inflation X.D X.E (enlarged X.D g) (enlarged X.E g)
      (Real.exp (logShape N X.D X.E X.U X.V))
      (Real.exp (logShape (parameter N (g ^ 2 * q)) (enlarged X.D g) (enlarged X.E g) (enlarged X.U q) (enlarged X.V q)))
      1 ((N : ℝ) ^ ε) (by linarith [X.D_ge_one]) (by linarith [X.E_ge_one])
      (by linarith [enlarged_ge_one X.D g]) (by linarith [enlarged_ge_one X.E g])
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by norm_num) hR
      (by simpa only [one_mul] using enlarged_le_original X.D g X.D_ge_one hg)
      (by simpa only [one_mul] using enlarged_le_original X.E g X.E_ge_one hg) hf
    simpa only [one_mul] using hc
  · have hc := pair_cost_inflation X.U X.V (enlarged X.U q) (enlarged X.V q)
      (Real.exp (logShape N X.D X.E X.U X.V))
      (Real.exp (logShape (parameter N (g ^ 2 * q)) (enlarged X.D g) (enlarged X.E g) (enlarged X.U q) (enlarged X.V q)))
      1 ((N : ℝ) ^ ε) (by linarith [X.U_ge_one]) (by linarith [X.V_ge_one])
      (by linarith [enlarged_ge_one X.U q]) (by linarith [enlarged_ge_one X.V q])
      (Real.exp_nonneg _) (Real.exp_nonneg _) (by norm_num) hR
      (by simpa only [one_mul] using enlarged_le_original X.U q X.U_ge_one hq)
      (by simpa only [one_mul] using enlarged_le_original X.V q X.V_ge_one hq) hf
    simpa only [one_mul] using hc

end PaperP1.ReducedDeterminantCosts
