module

public import PaperP1.Analysis.LogarithmicGaussianWindowScales
public import PaperP1.Analysis.SmoothGaussianWindowUpper


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformSmoothGaussianWindowUpper
open Finset Filter PaperP1 OddPrimePivot GaussianLaplaceKernel LogarithmicOrdinaryCensusBridge
  LogarithmicGaussianWindowScales
open scoped Classical

theorem uniform_bound (ε : ℝ) (hε : 0 < ε) : ∃ D : ℝ, 0 < D ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N ≥ N₀, ∀ Y j : ℕ, j ∈ Ico N (2*N) →
      ((Ico j (j+windowLength N)).filter fun n ↦ largestPrimeFactor n ≤ Y).card ≤ 1 →
      ∀ X : ℝ, (j : ℝ)+(windowLength N : ℝ)/2 ≤ X →
        X ≤ (j : ℝ)+(windowLength N : ℝ)/2+1 →
        ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y)
          (GaussianLogarithmicScales.shortWidth D N) (-Real.log X) ≤ ε := by
  have hP : 0 < prefactor 1 := prefactor_pos 1 (by norm_num)
  have hC : 0 < LogarithmicGaussianSum.constant := LogarithmicGaussianSum.constant_pos
  have hTailLimit : Tendsto (fun q : ℝ ↦ 5*prefactor 1*LogarithmicGaussianSum.constant*Real.exp (-q))
      atTop (nhds 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (5*prefactor 1*LogarithmicGaussianSum.constant)
  obtain ⟨QT,hTail⟩ := eventually_atTop.mp
    (hTailLimit.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<ε/2)))
  let q : ℝ := max 1 QT
  let D : ℝ := Real.sqrt (q/tailRate)
  have hq : 0 < q := by have hh : 1≤q := le_max_left _ _; linarith only [hh]
  have hD : 0 < D := Real.sqrt_pos.mpr (div_pos hq tailRate_pos)
  have hRate : tailRate*D^2=q := by
    dsimp only [D]
    rw [Real.sq_sqrt (div_nonneg hq.le tailRate_pos.le)]
    field_simp [tailRate_pos.ne']
  have hTailSmall : 5*prefactor 1*LogarithmicGaussianSum.constant*Real.exp (-tailRate*D^2) ≤ ε/2 := by
    rw [neg_mul,hRate]
    exact (hTail q (le_max_right _ _)).le
  obtain ⟨NG,hGeometry⟩ := eventually_atTop.mp (eventual_geometry D hD)
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hFirstLimit : Tendsto (fun N : ℕ ↦ prefactor 1*D/Real.log (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLogLimit
  obtain ⟨NF,hFirstTail⟩ := eventually_atTop.mp
    (hFirstLimit.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<ε/2)))
  refine ⟨D,hD,max 2 (max NG NF),by omega,?_⟩
  intro N hN Y j hj hFew X hXL hXR
  obtain ⟨hNN,hW,hWN,hDelta1,hMass,hLog⟩ := hGeometry N (by omega)
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hLP : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<N))
  let δ : ℝ := Real.log (N : ℝ)/(D*(N : ℝ))
  have hδ : 0 < δ := div_pos hLP (mul_pos hD hNP)
  have hNδ : 0 < (N : ℝ)*δ := mul_pos hNP hδ
  have hRecip : 1/((N : ℝ)*δ) ≤ 1 := (div_le_one hNδ).mpr hMass
  have hFirst : prefactor 1/((N : ℝ)*δ) ≤ ε/2 := by
    have he : prefactor 1/((N : ℝ)*δ)=prefactor 1*D/Real.log (N : ℝ) := by
      dsimp only [δ]
      field_simp
    rw [he]
    exact (hFirstTail N (by omega)).le
  let E : ℝ := Real.exp (-((windowLength N : ℝ)/(12*(N : ℝ)))^2/(8*δ^2))
  have hE : E ≤ Real.exp (-tailRate*D^2) := by
    have hh := neg_le_neg (tail_exponent_lower D hD N hNN hLog)
    apply Real.exp_le_exp.mpr
    change -((windowLength N : ℝ)/(12*(N : ℝ)))^2/
      (8*(Real.log (N : ℝ)/(D*(N : ℝ)))^2) ≤ -tailRate*D^2
    simpa only [neg_div,neg_mul] using hh
  have hTailBound : E*LogarithmicGaussianSum.constant*prefactor 1*
      (4+1/((N : ℝ)*δ)) ≤ ε/2 := by
    calc
      _ ≤ E*LogarithmicGaussianSum.constant*prefactor 1*5 := by
        apply mul_le_mul_of_nonneg_left (by linarith only [hRecip])
        dsimp only [E]
        positivity
      _ = 5*prefactor 1*LogarithmicGaussianSum.constant*E := by ring
      _ ≤ 5*prefactor 1*LogarithmicGaussianSum.constant*Real.exp (-tailRate*D^2) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
      _ ≤ _ := hTailSmall
  have hWindow := SmoothGaussianWindowUpper.window_bound N Y j (windowLength N)
    hNN hj hW hWN hFew δ X hδ hDelta1 hXL hXR
  have hExpand : (prefactor 1/((N : ℝ)*δ))*(1+E*LogarithmicGaussianSum.constant*(4*(N : ℝ)*δ+1)) =
      prefactor 1/((N : ℝ)*δ)+E*LogarithmicGaussianSum.constant*prefactor 1*(4+1/((N : ℝ)*δ)) := by
    field_simp
  change ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) (δ^2) (-Real.log X) ≤ ε
  change ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) (δ^2) (-Real.log X) ≤
    (prefactor 1/((N : ℝ)*δ))*(1+E*LogarithmicGaussianSum.constant*(4*(N : ℝ)*δ+1)) at hWindow
  rw [hExpand] at hWindow
  linarith only [hWindow,hFirst,hTailBound]

end PaperP1.UniformSmoothGaussianWindowUpper
