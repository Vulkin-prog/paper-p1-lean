module

public import PaperP1.Analysis.SmoothLowerBarrierGrowth
public import PaperP1.Arithmetic.PNTLogPrimePowerLower

/-! # An internal prime-weight margin paying the actual quotient loss

One pair of thresholds precedes every integer prime cutoff and every
barrier height in the stated exponent domain.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothLowerPrimeMargin

open Filter SmoothLowerBarrierProfile SmoothLowerBarrierGrowth

theorem uniform_weighted_margin (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, Real.exp 1 + 1 ≤ T ∧ ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
      ∀ Y ≥ Y₀, ∀ t ≥ T, tilt ε (t - 1) ≤ Real.log Y →
        t * Real.log Y ≤ (1 - 1 / (Y : ℝ)) *
          WeightedPrimeSum.logPrimeSum Y (1 - tilt ε (t - 1) / Real.log Y) := by
  obtain ⟨m, T₀, hm, _hT₀, hmargin⟩ := uniform_margin ε hε
  let g := (m - 1) / 4
  have hg : 0 < g := by dsimp only [g]; linarith only [hm]
  have hm0 : 0 < m := by linarith only [hm]
  let η := g / m
  have hη : 0 < η := div_pos hg hm0
  have hη1 : η < 1 := by
    apply (div_lt_iff₀ hm0).mpr
    dsimp only [g]
    linarith only [hm]
  have hidentity : (1 - η) * m = 1 + 3 * g := by
    dsimp only [η, g]
    field_simp
    ring
  obtain ⟨C, _hC, hprime⟩ := PNTLogPrimePowerLower.uniform_exponential_lower η hη hη1
  have hlogT : Tendsto (fun Y : ℕ ↦ Real.log Y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    ((hlogT.eventually (eventually_ge_atTop (C / g))).and
      ((tendsto_natCast_atTop_atTop (R := ℝ)).eventually
        (eventually_ge_atTop ((1 + 2 * g) / g))))
  refine ⟨max T₀ (Real.exp 1 + 1), le_max_right _ _, max Y₁ 2, by omega, ?_⟩
  intro Y hY t ht htilt
  obtain ⟨hlarge, hsize⟩ := hY₁ Y (by omega)
  have hy : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hy1 : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log Y := Real.log_pos hy1
  have htbase : Real.exp 1 + 1 ≤ t := (le_max_right _ _).trans ht
  have ht1 : 1 ≤ t := by have hh := Real.exp_pos 1; linarith only [htbase, hh]
  have ht0 : 0 < t := by linarith only [ht1]
  let ξ := tilt ε (t - 1)
  have hξ : 0 < ξ := by
    have hl := Real.log_le_log (Real.exp_pos 1) (by linarith only [htbase] : Real.exp 1 ≤ t - 1)
    rw [Real.log_exp] at hl
    have hll := Real.log_nonneg hl
    dsimp only [ξ, tilt]
    linarith only [hl, hll, hε]
  let δ := ξ / Real.log Y
  have hδ : 0 < δ := div_pos hξ hlogY
  have hδ1 : δ ≤ 1 := (div_le_iff₀ hlogY).mpr (by simpa only [one_mul] using htilt)
  have harg : δ * Real.log Y = ξ := by dsimp only [δ]; field_simp
  have hp := hprime δ hδ hδ1 Y (by omega)
  rw [harg] at hp
  have hnorm : (Real.exp ξ - 2) / δ = Real.log Y * (t * primeMargin ε t) := by
    dsimp only [δ, ξ, primeMargin]
    field_simp
  rw [hnorm] at hp
  have hmarg := hmargin t ((le_max_left _ _).trans ht)
  have hcompare : (1 - η) * m * (t * Real.log Y) - C ≤ WeightedPrimeSum.logPrimeSum Y (1 - δ) := by
    have hs := mul_le_mul_of_nonneg_left hmarg
      (show 0 ≤ (1 - η) * (t * Real.log Y) by positivity)
    have hh : (1 - η) * m * (t * Real.log Y) ≤ (1 - η) * (Real.log Y * (t * primeMargin ε t)) := by
      nlinarith only [hs]
    exact (sub_le_sub_right hh C).trans hp
  rw [hidentity] at hcompare
  have hCsmall : C ≤ g * (t * Real.log Y) := by
    have hc := (div_le_iff₀ hg).mp hlarge
    have hh : g * Real.log Y ≤ g * (t * Real.log Y) := by
      nlinarith only [mul_nonneg (by positivity : 0 ≤ g * Real.log Y) (sub_nonneg.mpr ht1)]
    exact (by nlinarith only [hc] : C ≤ g * Real.log Y).trans hh
  have hlower : (1 + 2 * g) * (t * Real.log Y) ≤ WeightedPrimeSum.logPrimeSum Y (1 - δ) := by
    nlinarith only [hcompare, hCsmall]
  have hfactor0 : 0 ≤ 1 - 1 / (Y : ℝ) := by
    have hh : 1 / (Y : ℝ) ≤ 1 := (div_le_iff₀ hy).mpr (by simpa only [one_mul] using hy1.le)
    linarith only [hh]
  have hfactor : 1 ≤ (1 - 1 / (Y : ℝ)) * (1 + 2 * g) := by
    have hs := (div_le_iff₀ hg).mp hsize
    have hid : (1 - 1 / (Y : ℝ)) * (1 + 2 * g) = (((Y : ℝ) - 1) * (1 + 2 * g)) / Y := by
      field_simp
    rw [hid]
    apply (le_div_iff₀ hy).mpr
    nlinarith only [hs, hg]
  calc
    _ ≤ ((1 - 1 / (Y : ℝ)) * (1 + 2 * g)) * (t * Real.log Y) :=
      le_mul_of_one_le_left (by positivity) hfactor
    _ = (1 - 1 / (Y : ℝ)) * ((1 + 2 * g) * (t * Real.log Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower hfactor0

end PaperP1.SmoothLowerPrimeMargin
