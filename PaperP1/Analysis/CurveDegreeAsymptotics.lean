module

public import PaperP1.Analysis.CurveDegreeProfile
public import PaperP1.Arithmetic.PrimeLogBudget
public import PaperP1.PNT.LogGrowth

/-! # Uniform sublinearity of the degree-dependent analytic point-count factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveDegreeAsymptotics

open Filter PaperP1.CurveDegreeProfile

def envelope (c b κ : ℝ) (B : ℕ) : ℝ :=
  (8 * c ^ (1 / 2 : ℝ)) * (Real.log B ^ κ / (B : ℝ) ^ (1 / 2 : ℝ)) +
    (2 * Real.exp 1) * (Real.log B ^ κ / (B : ℝ) ^ (1 - 2 * b))

theorem envelope_tendsto_zero (c b κ : ℝ) (hb : b < 1 / 2) :
    Tendsto (envelope c b κ) atTop (nhds 0) := by
  have h₁ := (PNT.tendsto_pow_log_div_pow_atTop (1 / 2) κ (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h₂ := (PNT.tendsto_pow_log_div_pow_atTop (1 - 2 * b) κ (by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto (fun B : ℕ ↦ envelope c b κ B) atTop (nhds 0)
  simpa only [envelope, Function.comp_def, mul_zero, add_zero] using
    (h₁.const_mul (8 * c ^ (1 / 2 : ℝ))).add (h₂.const_mul (2 * Real.exp 1))

theorem logarithmic_weights_eventually (c κ : ℝ) (hc : 0 < c) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀,
      2 < c * (B : ℝ) ∧ Real.log (c * B) ≤ 2 * Real.log B ∧
        Real.log (c * B) ^ κ ≤ 2 * Real.log B ^ κ := by
  have hr := PrimeLogBudget.log_mul_div_log_tendsto c hc
  have hp : Tendsto (fun B : ℕ ↦ (Real.log (c * B) / Real.log B) ^ κ) atTop (nhds 1) := by
    simpa only [Real.one_rpow] using hr.rpow_const (Or.inl one_ne_zero)
  obtain ⟨B₁, hB₁⟩ := eventually_atTop.mp
    ((hr.eventually (eventually_lt_nhds (show (1 : ℝ) < 2 by norm_num))).and
      (hp.eventually (eventually_lt_nhds (show (1 : ℝ) < 2 by norm_num))))
  obtain ⟨B₂, hB₂⟩ := exists_nat_gt (3 / c)
  refine ⟨max 2 (max B₁ B₂), by omega, ?_⟩
  intro B hB
  have hBtwo : 2 ≤ B := by omega
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hlog : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlarge : 3 / c < (B : ℝ) := hB₂.trans_le (by exact_mod_cast (show B₂ ≤ B by omega))
  have hheight : 2 < c * (B : ℝ) := by
    have h := (div_lt_iff₀ hc).mp hlarge
    nlinarith
  have hHlog : 0 < Real.log (c * B) := Real.log_pos (by linarith)
  obtain ⟨hrB, hpB⟩ := hB₁ B (by omega)
  refine ⟨hheight, ((div_lt_iff₀ hlog).mp hrB).le, ?_⟩
  rw [Real.div_rpow hHlog.le hlog.le κ] at hpB
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hlog κ)).mp hpB).le

theorem power_div_scale (B t : ℝ) (hB : 0 < B) :
    B ^ t / B = 1 / B ^ (1 - t) := by
  rw [Real.rpow_sub hB, Real.rpow_one, one_div_div]

theorem degree_uniform_eventually (c b κ : ℝ) (hc : 0 < c) (hb : 0 < b) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ D : ℝ, 2 ≤ D → D ≤ (B : ℝ) ^ b →
      profile (c * B) D * Real.log (c * B) ^ κ / B ≤ envelope c b κ B := by
  obtain ⟨B₁, hB₁, hweights⟩ := logarithmic_weights_eventually c κ hc
  have hs := ((PNT.tendsto_pow_log_div_pow_atTop b 1 hb).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
  obtain ⟨B₂, hB₂⟩ := eventually_atTop.mp hs
  refine ⟨max B₁ B₂, by omega, ?_⟩
  intro B hB D hD hDM
  obtain ⟨hheight, hlogup, hweight⟩ := hweights B (by omega)
  have hBtwo : 2 ≤ B := by omega
  have hBp : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hpow : 0 < (B : ℝ) ^ b := Real.rpow_pos_of_pos hBp b
  have hsmall : Real.log B / (B : ℝ) ^ b ≤ 1 / 2 := by
    simpa only [Real.rpow_one, Function.comp_def] using (hB₂ B (by omega)).le
  have hlog : Real.log (c * B) ≤ (B : ℝ) ^ b := by
    have hm := (div_le_iff₀ hpow).mp hsmall
    linarith
  have hdegree := degree_uniform_bound (c * B) D ((B : ℝ) ^ b) (by linarith) hD hDM hlog
  have hm : ((B : ℝ) ^ b) ^ 2 = (B : ℝ) ^ (2 * b) := by
    rw [← Real.rpow_mul_natCast hBp.le b 2]
    congr 1
    ring
  rw [Real.mul_rpow hc.le hBp.le, hm] at hdegree
  have hlogH : 0 ≤ Real.log (c * B) := Real.log_nonneg (by linarith)
  have hprod := mul_le_mul hdegree hweight (Real.rpow_nonneg hlogH κ) (by positivity)
  have hdiv := div_le_div_of_nonneg_right hprod hBp.le
  refine hdiv.trans_eq ?_
  calc
    ((4 * (c ^ (1 / 2 : ℝ) * (B : ℝ) ^ (1 / 2 : ℝ)) + Real.exp 1 * (B : ℝ) ^ (2 * b)) *
        (2 * Real.log B ^ κ)) / B =
      (8 * c ^ (1 / 2 : ℝ)) * Real.log B ^ κ * ((B : ℝ) ^ (1 / 2 : ℝ) / B) +
        (2 * Real.exp 1) * Real.log B ^ κ * ((B : ℝ) ^ (2 * b) / B) := by ring
    _ = envelope c b κ B := by
      rw [power_div_scale (B : ℝ) (1 / 2) hBp, power_div_scale (B : ℝ) (2 * b) hBp]
      norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      unfold envelope
      ring

theorem uniform_sublinear (c b κ : ℝ) (hc : 0 < c) (hb : 0 < b) (hb₁ : b < 1 / 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 2 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ D : ℝ, 2 ≤ D → D ≤ (B : ℝ) ^ b →
      profile (c * B) D * Real.log (c * B) ^ κ ≤ ε * B := by
  obtain ⟨B₁, hB₁, hbound⟩ := degree_uniform_eventually c b κ hc hb
  obtain ⟨B₂, hB₂⟩ := eventually_atTop.mp
    ((envelope_tendsto_zero c b κ hb₁).eventually (eventually_lt_nhds hε))
  refine ⟨max B₁ B₂, by omega, ?_⟩
  intro B hB D hD hDM
  have hm := (hbound B (by omega) D hD hDM).trans (hB₂ B (by omega)).le
  exact (div_le_iff₀ (by exact_mod_cast (show 0 < B by omega) : (0 : ℝ) < B)).mp hm

end PaperP1.CurveDegreeAsymptotics
