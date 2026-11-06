module

public import PaperP1.Analysis.GaussianDirichletTail
public import PaperP1.Analysis.SmoothLongLengthGeometry
public import PaperP1.PNT.LogGrowth


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GaussianLogarithmicScales
open Filter PaperP1
open scoped Classical

def shortWidth (D : ℝ) (N : ℕ) : ℝ := (Real.log (N : ℝ)/(D*(N : ℝ)))^2

def longWidth (N : ℕ) : ℝ := ((SmoothLongMeanStability.length N : ℝ)/(N : ℝ))^2

def height (D L : ℝ) (N : ℕ) : ℝ := D*Real.sqrt L*(N : ℝ)/Real.log (N : ℝ)

def uniformBudget : ℝ := Real.sqrt Real.pi+4*Real.pi

theorem shortWidth_pos (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 2 ≤ N) : 0 < shortWidth D N := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  unfold shortWidth
  exact sq_pos_of_pos (div_pos (Real.log_pos hNR) (mul_pos hD (by linarith only [hNR])))

theorem longWidth_pos (N : ℕ) (hN : 2 ≤ N) : 0 < longWidth N := by
  have hLen : 0 < (SmoothLongMeanStability.length N : ℝ) := by
    exact_mod_cast SmoothLongMeanStability.length_pos N hN
  unfold longWidth
  exact sq_pos_of_pos (div_pos hLen (by exact_mod_cast (by omega : 0<N)))

theorem logarithmic_ratio_tendsto :
    Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  simpa only [Function.comp_def,Real.rpow_one] using
    (PNT.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem shortWidth_tendsto (D : ℝ) : Tendsto (shortWidth D) atTop (nhds 0) := by
  have hh := (logarithmic_ratio_tendsto.div_const D).pow 2
  change Tendsto (fun N : ℕ ↦ (Real.log (N : ℝ)/(D*(N : ℝ)))^2) atTop (nhds 0)
  simpa only [zero_div,zero_pow (by decide : (2 : ℕ)≠0),div_div,mul_comm] using hh

theorem longWidth_tendsto : Tendsto longWidth atTop (nhds 0) := by
  change Tendsto (fun N : ℕ ↦ ((SmoothLongMeanStability.length N : ℝ)/(N : ℝ))^2) atTop (nhds 0)
  simpa only [zero_pow (by decide : (2 : ℕ)≠0)] using SmoothLongLengthGeometry.relative_size_tendsto.pow 2

theorem eventual_order (D : ℝ) (hD : 0 < D) : ∀ᶠ N : ℕ in atTop, shortWidth D N ≤ longWidth N := by
  have hRatio : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Real.rpow_one,Real.sqrt_eq_rpow] using
      (PNT.tendsto_pow_log_div_pow_atTop (1/2) 1 (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 2,hRatio.eventually (eventually_lt_nhds hD)] with N hN hSmall
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hRoot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNP
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hLogLen : Real.log (N : ℝ) ≤ D*(SmoothLongMeanStability.length N : ℝ) :=
    ((div_le_iff₀ hRoot).mp hSmall.le).trans
      (mul_le_mul_of_nonneg_left (SmoothLongLengthGeometry.length_sqrt_lower N hN) hD.le)
  have hRatioLen : Real.log (N : ℝ)/(D*(N : ℝ)) ≤ (SmoothLongMeanStability.length N : ℝ)/(N : ℝ) := by
    have hh := div_le_div_of_nonneg_right ((div_le_iff₀ hD).mpr (by simpa only [mul_comm] using hLogLen)) hNP.le
    simpa only [div_div] using hh
  exact pow_le_pow_left₀ (by positivity) hRatioLen 2

theorem budget_identity (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 2 ≤ N) :
    GaussianDirichletTail.budget N (shortWidth D N) = Real.sqrt Real.pi*D/Real.log (N : ℝ)+4*Real.pi := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  rw [GaussianDirichletTail.budget,shortWidth,Real.sqrt_div Real.pi_pos.le,
    Real.sqrt_sq (by positivity)]
  field_simp

theorem budget_bound (D : ℝ) (hD : 0 < D) (N : ℕ) (hN : 2 ≤ N) (hLog : D ≤ Real.log (N : ℝ)) :
    GaussianDirichletTail.budget N (shortWidth D N) ≤ uniformBudget := by
  have hLP : 0 < Real.log (N : ℝ) := hD.trans_le hLog
  rw [budget_identity D hD N hN]
  unfold uniformBudget
  have hh := mul_le_mul_of_nonneg_left ((div_le_one hLP).mpr hLog) (Real.sqrt_nonneg Real.pi)
  calc
    _ = Real.sqrt Real.pi*(D/Real.log (N : ℝ))+4*Real.pi := by ring
    _ ≤ Real.sqrt Real.pi*1+4*Real.pi := add_le_add hh le_rfl
    _ = _ := by ring

theorem height_product (D L : ℝ) (hD : 0 < D) (hL : 0 ≤ L) (N : ℕ) (hN : 2 ≤ N) :
    shortWidth D N*(height D L N)^2=L := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  unfold shortWidth height
  field_simp
  nlinarith only [Real.sq_sqrt hL]

theorem height_tendsto (D L : ℝ) (hD : 0 < D) (hL : 0 < L) :
    Tendsto (height D L) atTop atTop := by
  have hPos : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ)/(N : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
    exact div_pos (Real.log_pos hNR) (by linarith only [hNR])
  have hGT : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/(N : ℝ)) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨logarithmic_ratio_tendsto,hPos⟩
  have hRec : Tendsto (fun N : ℕ ↦ (N : ℝ)/Real.log (N : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,inv_div] using tendsto_inv_nhdsGT_zero.comp hGT
  have hConst : Tendsto (fun _N : ℕ ↦ D*Real.sqrt L) atTop (nhds (D*Real.sqrt L)) :=
    tendsto_const_nhds
  have hRes := hConst.pos_mul_atTop (mul_pos hD (Real.sqrt_pos.mpr hL)) hRec
  change Tendsto (fun N : ℕ ↦ D*Real.sqrt L*(N : ℝ)/Real.log (N : ℝ)) atTop atTop
  simpa only [mul_div_assoc] using hRes

theorem central_error_tendsto (D R : ℝ) :
    Tendsto (fun N : ℕ ↦ 2*(shortWidth D N+longWidth N)^2*R^5) atTop (nhds 0) := by
  simpa only [zero_add,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_mul] using
    ((((shortWidth_tendsto D).add longWidth_tendsto).pow 2).const_mul 2).mul_const (R^5)

end PaperP1.GaussianLogarithmicScales
