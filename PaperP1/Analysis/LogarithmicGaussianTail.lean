module

public import PaperP1.Analysis.LogarithmicGaussianSum
public import PaperP1.Analysis.GaussianFrequencyTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicGaussianTail
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def height (X : ℕ) : ℝ := (Real.log (X : ℝ))^10

def tailEnvelope (X : ℕ) : ℝ := Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2*
  GaussianFrequencyTail.tailBound ((LogarithmicGaussianSum.width X)^2) (height X)

def constant : ℝ := 4*Real.sqrt (2*Real.pi)

theorem height_positive (X : ℕ) (hX : 2 ≤ X) : 0 < height X := by
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  dsimp only [height]
  positivity

theorem tail_identity (X : ℕ) (hX : 2 ≤ X) :
    GaussianFrequencyTail.tailBound ((LogarithmicGaussianSum.width X)^2) (height X)=
      Real.exp (-(Real.log (X : ℝ))^4/2)*Real.sqrt (2*Real.pi)*(Real.log (X : ℝ))^8 := by
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he : -((LogarithmicGaussianSum.width X)^2)*(height X)^2/2=-(Real.log (X : ℝ))^4/2 := by
    dsimp only [LogarithmicGaussianSum.width,height]
    field_simp [hl.ne']
  have hr : Real.pi/((LogarithmicGaussianSum.width X)^2/2)=
      (2*Real.pi)*((Real.log (X : ℝ))^8)^2 := by
    dsimp only [LogarithmicGaussianSum.width]
    field_simp [hl.ne']
  rw [GaussianFrequencyTail.tailBound,he,hr,Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),Real.sqrt_sq (by positivity : 0 ≤ (Real.log (X : ℝ))^8)]
  ring

theorem exponential_bound (X : ℕ) (hlog : 2 ≤ Real.log (X : ℝ)) :
    Real.exp (-(Real.log (X : ℝ))^4/2) ≤ 1/(X : ℝ) := by
  have hX : (0 : ℝ) < X := lt_of_le_of_ne (Nat.cast_nonneg X) (by
    intro he
    rw [← he,Real.log_zero] at hlog
    norm_num at hlog)
  have hsmall : Real.log (X : ℝ) ≤ (Real.log (X : ℝ))^4/2 := by
    have hl : 0 ≤ Real.log (X : ℝ) := by linarith
    have hs : 4 ≤ (Real.log (X : ℝ))^2 := by nlinarith
    have hm := mul_nonneg hl (show 0 ≤ Real.log (X : ℝ)-2 by linarith)
    nlinarith [sq_nonneg ((Real.log (X : ℝ))^2-1)]
  calc
    _ ≤ Real.exp (-Real.log (X : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg,Real.exp_log hX,one_div]


theorem tailEnvelope_nonneg (X : ℕ) : 0 ≤ tailEnvelope X := by
  dsimp only [tailEnvelope,GaussianFrequencyTail.tailBound]
  exact mul_nonneg (mul_nonneg (Real.log_natCast_nonneg X) (sq_nonneg _))
    (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))

theorem tailEnvelope_bound (X : ℕ) (hX : 2 ≤ X)
    (hlog : max 2 (Real.log 4+4) ≤ Real.log (X : ℝ)) :
    tailEnvelope X ≤ constant*(Real.log (X : ℝ))^11/(X : ℝ) := by
  have hl2 := (le_max_left 2 (Real.log 4+4)).trans hlog
  have hlB := (le_max_right 2 (Real.log 4+4)).trans hlog
  have hl : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hB : 0 ≤ Real.log 4+4 := by have hh := Real.log_natCast_nonneg 4; norm_num at hh; linarith
  have hpow := pow_le_pow_left₀ (show 0 ≤ Real.log (X : ℝ)+(Real.log 4+4) by linarith)
    (show Real.log (X : ℝ)+(Real.log 4+4) ≤ 2*Real.log (X : ℝ) by linarith) 2
  have hp : Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2 ≤ 4*(Real.log (X : ℝ))^3 := by
    have hh := mul_le_mul_of_nonneg_left hpow hl
    nlinarith
  have he := exponential_bound X hl2
  have hm := mul_le_mul hp he (Real.exp_pos _).le (by positivity : 0 ≤ 4*(Real.log (X : ℝ))^3)
  have hh := mul_le_mul_of_nonneg_right hm
    (mul_nonneg (Real.sqrt_nonneg (2*Real.pi)) (pow_nonneg hl 8))
  calc
    _ = (Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2*Real.exp (-(Real.log (X : ℝ))^4/2))*
        (Real.sqrt (2*Real.pi)*(Real.log (X : ℝ))^8) := by rw [tailEnvelope,tail_identity X hX]; ring
    _ ≤ (4*(Real.log (X : ℝ))^3*(1/(X : ℝ)))*(Real.sqrt (2*Real.pi)*(Real.log (X : ℝ))^8) := hh
    _ = _ := by dsimp only [constant]; ring

theorem tailEnvelope_tendsto : Tendsto tailEnvelope atTop (nhds 0) := by
  have hnat : Tendsto (fun X : ℕ ↦ (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := Real.tendsto_log_atTop.comp hnat
  have hlim : Tendsto (fun X : ℕ ↦ constant*(Real.log (X : ℝ))^11/(X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Real.rpow_ofNat,Function.comp_def,mul_zero,mul_div_assoc] using
      ((PNT.tendsto_pow_log_div_pow_atTop 1 11 zero_lt_one).comp hnat).const_mul constant
  have hbound : ∀ᶠ X : ℕ in atTop, tailEnvelope X ≤ constant*(Real.log (X : ℝ))^11/(X : ℝ) := by
    filter_upwards [eventually_ge_atTop 2,hlog.eventually (eventually_ge_atTop (max 2 (Real.log 4+4)))] with X hX hl
    exact tailEnvelope_bound X hX hl
  exact squeeze_zero' (Filter.Eventually.of_forall tailEnvelope_nonneg) hbound hlim

theorem tailEnvelope_small (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, tailEnvelope X ≤ ε := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (tailEnvelope_tendsto.eventually (eventually_lt_nhds hε))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX
  exact (hX₀ X ((le_max_left _ _).trans hX)).le
end PaperP1.LogarithmicGaussianTail
