module

public import PaperP1.Analysis.ReducedSourceParameter

/-! # A uniform short-shift margin retains both reduced source logarithmic hypotheses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedSourceLogarithms

open PaperP1.DeterminantSourceBox PaperP1.ReducedDyadicScales PaperP1.ReducedSourceParameter

theorem uniform_shift_margin (K A δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h : ℕ, 0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A →
      1 ≤ N ∧ (h : ℝ) ≤ Real.sqrt N ∧ Real.log h ≤ (δ / 4) * Real.log N := by
  let θ := min (1 / 2 : ℝ) (δ / 4)
  have hθ : 0 < θ := lt_min (by norm_num) (by positivity)
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow K A θ hθ
  refine ⟨max 1 Nh, ?_⟩
  intro N hN h hh hshift
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < N := by linarith
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hp : (h : ℝ) ≤ (N : ℝ) ^ θ := hshift.trans (hNh N (by omega))
  have hhalf : (h : ℝ) ≤ Real.sqrt N := by
    have ht := hp.trans (Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left _ _))
    simpa only [Real.sqrt_eq_rpow] using ht
  have hsmall : (h : ℝ) ≤ (N : ℝ) ^ (δ / 4) :=
    hp.trans (Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right _ _))
  have hlog := Real.log_le_log hhR hsmall
  rw [Real.log_rpow hn] at hlog
  exact ⟨by omega, hhalf, hlog⟩

theorem reduced_log_bounds {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (hN : 1 ≤ N) (hδ : 0 < δ)
    (h g q : ℕ) (_hh : 0 < h) (hg : 0 < g) (hq : 0 < q) (hscale : g ^ 2 * q ≤ h)
    (hlogh : Real.log h ≤ (δ / 4) * Real.log N) :
    (δ / 2) * Real.log (parameter N (g ^ 2 * q)) ≤ Real.log (enlarged X.D g * enlarged X.E g) ∧
      (δ / 2) * Real.log (parameter N (g ^ 2 * q)) ≤ Real.log (enlarged X.U q * enlarged X.V q) := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hg2h : g ^ 2 ≤ h := (Nat.le_mul_of_pos_right _ hq).trans hscale
  have hqh : q ≤ h := (Nat.le_mul_of_pos_left _ (pow_pos hg 2)).trans hscale
  have hlogg : 2 * Real.log g ≤ Real.log h := by
    have ht := Real.log_le_log (pow_pos hgR 2) (by exact_mod_cast hg2h : (g : ℝ) ^ 2 ≤ h)
    rw [Real.log_pow] at ht
    simpa only [Nat.cast_ofNat] using ht
  have hlogq : Real.log q ≤ Real.log h := Real.log_le_log hqR (by exact_mod_cast hqh)
  have hparam := parameter_log_upper N (g ^ 2 * q) (by omega) (Nat.mul_pos (pow_pos hg 2) hq)
  have hparamδ := mul_le_mul_of_nonneg_left hparam (by positivity : 0 ≤ δ / 2)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hδlogN := mul_nonneg hδ.le hlogN
  have hDE := log_product_lower X.D X.E g (by linarith [X.D_ge_one]) (by linarith [X.E_ge_one]) hg
  have hUV := log_product_lower X.U X.V q (by linarith [X.U_ge_one]) (by linarith [X.V_ge_one]) hq
  constructor
  · nlinarith only [hparamδ, hDE, X.first_log, hlogg, hlogh, hδlogN]
  · nlinarith only [hparamδ, hUV, X.second_log, hlogq, hlogh]

end PaperP1.ReducedSourceLogarithms
