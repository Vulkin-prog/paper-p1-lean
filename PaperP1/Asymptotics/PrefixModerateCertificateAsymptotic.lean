module

public import PaperP1.Asymptotics.ModerateFactorialBudget
public import PaperP1.Arithmetic.PrefixModerateWeightedSeries
public import PaperP1.Model.LocalRigidityConsequences

/-! # The weighted growing-order conclusion of the moderate-certificate lemma -/

/-! The centre range in this module is the positive prefix [2,N+2),
with exactly N centres; no critical lower bound on a centre is assumed. -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixModerateCertificateAsymptotic

open Filter PaperP1.ModerateOrder PaperP1.PrefixModerateWeightedSeries

theorem constant_le_power_eventually (K ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, K ≤ (N : ℝ) ^ ε :=
  ((tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (eventually_ge_atTop K)

theorem cutoff_ge_log_eventually (A D : ℝ) (hA : 1 < A) :
    ∀ᶠ N : ℕ in atTop, D * Real.log N ≤ cutoff A N := by
  have hlim := (tendsto_rpow_atTop (by linarith : 0 < A - 1)).comp
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop D),
    PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 1)] with N h hH
  have hHpos : 0 < Real.log N := by linarith
  calc
    _ ≤ (Real.log N) ^ (A - 1) * Real.log N := mul_le_mul_of_nonneg_right h hHpos.le
    _ = (Real.log N) ^ ((A - 1) + 1) := by rw [Real.rpow_add hHpos, Real.rpow_one]
    _ = cutoff A N := by unfold cutoff; congr 1; ring

def exponentialConstant (M : ℝ) : ℝ := 18 * Real.exp (Real.exp 1 * (2 * M))

theorem weightedTotal_le_power_eventually (A β D M ε : ℝ)
    (hA : 1 < A) (hβ : 0 ≤ β) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B : ℕ, 2 ≤ B → B ≤ N + 1 → (B : ℝ) ≤ D * Real.log N →
      ∀ a : ℝ, 0 ≤ a → a * N ≤ M →
        weightedTotal B N (cutoff A N) ((N : ℝ) ^ β) a ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
  have hhalf : 0 < ε / 2 := by linarith
  filter_upwards [PaperP1.ModerateFactorialBudget.product_le_power_eventually A D (ε / 2)
      (by linarith) hD hhalf,
    cutoff_ge_log_eventually A D hA,
    constant_le_power_eventually (exponentialConstant M) (ε / 2) hhalf,
    eventually_ge_atTop 10] with N hbudget hcut hconstant hN B hB hBN hwidth a ha hmean
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hT : 1 ≤ (N : ℝ) ^ β := Real.one_le_rpow hNone hβ
  have hY := hwidth.trans hcut
  have hfinite := weightedTotal_le B N hN hB hBN (cutoff A N) ((N : ℝ) ^ β) a hY hT ha
  have hexp : Real.exp (Real.exp 1 * (2 * a * N)) ≤ Real.exp (Real.exp 1 * (2 * M)) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmean (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1)
    nlinarith
  have hpref : 0 ≤ coefficient B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) + 1).factorial : ℝ) := by
    unfold coefficient
    positivity
  have hfinite' := hfinite.trans (mul_le_mul_of_nonneg_left hexp hpref)
  have hdenom : ((N : ℝ) ^ β) ^ 2 = (N : ℝ) ^ (2 * β) := by
    rw [← Real.rpow_mul_natCast hNpos.le β 2]
    congr 1
    ring
  have hrew : coefficient B N (cutoff A N) ((N : ℝ) ^ β) *
      ((PaperP1.PrimeProductBudget.assignmentExponent N (cutoff A N) + 1).factorial : ℝ) *
        Real.exp (Real.exp 1 * (2 * M)) =
      exponentialConstant M * ((B : ℝ) ^ (order A N + 4) * ((order A N + 1).factorial : ℝ)) /
        (N : ℝ) ^ (2 * β) := by
    unfold coefficient exponentialConstant order
    rw [hdenom]
    ring
  rw [hrew] at hfinite'
  have hprod := hbudget B (by omega) hwidth
  have hK : 0 ≤ exponentialConstant M := by unfold exponentialConstant; positivity
  calc
    _ ≤ exponentialConstant M *
        ((B : ℝ) ^ (order A N + 4) * ((order A N + 1).factorial : ℝ)) / (N : ℝ) ^ (2 * β) := hfinite'
    _ ≤ exponentialConstant M * (N : ℝ) ^ (4 / A + ε / 2) / (N : ℝ) ^ (2 * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hK) (Real.rpow_nonneg hNpos.le _)
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (4 / A + ε / 2) / (N : ℝ) ^ (2 * β) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hNpos.le _))
        (Real.rpow_nonneg hNpos.le _)
    _ = _ := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_sub hNpos]
      congr 1
      ring


end PaperP1.PrefixModerateCertificateAsymptotic
