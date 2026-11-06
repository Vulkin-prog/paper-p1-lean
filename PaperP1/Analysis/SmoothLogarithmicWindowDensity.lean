module

public import PaperP1.Analysis.SmoothLongGaussianLower
public import PaperP1.Analysis.LogarithmicCellSquareBudget
public import PaperP1.Analysis.CompleteShortAverage
public import PaperP1.Analysis.LogarithmicGaussianWindowScales
public import PaperP1.Analysis.UniformSmoothGaussianWindowUpper


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothLogarithmicWindowDensity
open Finset Filter MeasureTheory PaperP1 OddPrimePivot LogarithmicOrdinaryCensusBridge
open scoped Classical

def badWindows (N Y : ℕ) : Finset ℕ := (Ico N (2*N)).filter fun j ↦
  ((Ico j (j+windowLength N)).filter fun n ↦ largestPrimeFactor n ≤ Y).card ≤ 1

def interiorBad (N Y : ℕ) : Finset ℕ := (badWindows N Y).filter fun j ↦ j+windowLength N ≤ 2*N

theorem boundary_bound (N Y : ℕ) (hW : windowLength N ≤ N) :
    (badWindows N Y).card ≤ (interiorBad N Y).card+windowLength N := by
  have hSub : badWindows N Y ⊆ interiorBad N Y ∪ Ico (2*N-windowLength N) (2*N) := by
    intro j hj
    by_cases hInside : j+windowLength N ≤ 2*N
    · exact mem_union_left _ (mem_filter.mpr ⟨hj,hInside⟩)
    · apply mem_union_right
      have hjB := mem_Ico.mp (mem_filter.mp hj).1
      exact mem_Ico.mpr ⟨by omega,hjB.2⟩
  have hCard := (card_le_card hSub).trans (card_union_le _ _)
  rw [Nat.card_Ico,show 2*N-(2*N-windowLength N)=windowLength N by omega] at hCard
  exact hCard

theorem uniform_bound (a : ℝ) (ha : 0 < a) (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((badWindows N ⌊(N : ℝ)^a⌋₊).card : ℝ) ≤ τ*(N : ℝ) := by
  obtain ⟨κ,hκ,NL,hNL,hLong⟩ := SmoothLongGaussianLower.uniform_lower a ha
  obtain ⟨D,hD,NS,hNS,hShort⟩ := UniformSmoothGaussianWindowUpper.uniform_bound (κ/2) (by positivity)
  obtain ⟨NE,hNE,hEnergyBound⟩ := ActualGaussianMeanComparison.uniform_bound D hD
    (τ*(κ/2)^2/8) (by positivity)
  obtain ⟨NG,hGeometry⟩ := eventually_atTop.mp (LogarithmicGaussianWindowScales.eventual_geometry D hD)
  obtain ⟨NW,hWindowTail⟩ := eventually_atTop.mp
    (LogarithmicGaussianWindowScales.relative_length_tendsto.eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ)<τ/2)))
  refine ⟨max 2 (max NL (max NS (max NE (max NG NW)))),by omega,?_⟩
  intro N hN
  obtain ⟨hNN,hW6,hWN,hDelta,hMass,hLog⟩ := hGeometry N (by omega)
  have hNP : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0<N)
  have hW6R : (6 : ℝ) ≤ windowLength N := by exact_mod_cast hW6
  have hWNR : (windowLength N : ℝ) ≤ N := by exact_mod_cast hWN
  let Y := ⌊(N : ℝ)^a⌋₊
  have hY : 1 ≤ Y := PowerSelbergLevel.level_pos a (N : ℝ) ha.le
    (by exact_mod_cast (by omega : 1≤N))
  let f := CompleteShortAverage.smoothHom Y hY
  let b := GaussianLogarithmicScales.shortWidth D N
  let c := GaussianLogarithmicScales.longWidth N
  let G : ℝ → ℝ := fun u ↦ ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) b u-
    ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) c u
  let shift : ℝ := (windowLength N : ℝ)/2
  let B := interiorBad N Y
  have hb : 0 < b := GaussianLogarithmicScales.shortWidth_pos D hD N hNN
  have hc : 0 < c := GaussianLogarithmicScales.longWidth_pos N hNN
  have hGI : Integrable (fun u ↦ (G u)^2) :=
    ActualGaussianMeanComparison.difference_integrable N (OrdinarySmoothIndicator.value Y) b c hb hc
  have hEnergy : (∫ u : ℝ, (G u)^2) ≤ τ*(κ/2)^2/8 :=
    hEnergyBound N (by omega) f (CompleteShortAverage.smoothHom_prime_bound Y hY)
  have hCellGap : ∀ j ∈ B, ∀ u ∈ LogarithmicWindowCells.cell shift j, κ/2 ≤ |G u| := by
    intro j hj u hu
    obtain ⟨hjBad,hjEnd⟩ := mem_filter.mp hj
    obtain ⟨hjBand,hjFew⟩ := mem_filter.mp hjBad
    have hjNR : (N : ℝ) ≤ j := by exact_mod_cast (mem_Ico.mp hjBand).1
    have hEnd : (j : ℝ)+(windowLength N : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hjEnd
    have hBase : 0 < (j : ℝ)+shift := by dsimp only [shift]; linarith only [hNP,hjNR,hW6R]
    have hTop : 0 < (j : ℝ)+shift+1 := by linarith only [hBase]
    let X : ℝ := Real.exp (-u)
    have hXL : (j : ℝ)+(windowLength N : ℝ)/2 ≤ X := by
      have hExp := Real.exp_le_exp.mpr (show Real.log ((j : ℝ)+shift) ≤ -u by
        have hh := (Set.mem_Ioc.mp hu).2
        linarith only [hh])
      rw [Real.exp_log hBase] at hExp
      exact hExp
    have hXR : X ≤ (j : ℝ)+(windowLength N : ℝ)/2+1 := by
      have hExp := Real.exp_lt_exp.mpr (show -u < Real.log ((j : ℝ)+shift+1) by
        have hh := (Set.mem_Ioc.mp hu).1
        linarith only [hh])
      rw [Real.exp_log hTop] at hExp
      exact hExp.le
    have hNXL : (N : ℝ) ≤ X := by linarith only [hjNR,hXL,hW6R]
    have hXplus : X+1 ≤ 2*(N : ℝ) := by linarith only [hXR,hEnd,hW6R]
    have hCenter : -Real.log X=u := by dsimp only [X]; rw [Real.log_exp]; ring
    have hShortU : ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) b u ≤ κ/2 := by
      have hh := hShort N (by omega) Y j hjBand hjFew X hXL hXR
      simpa only [hCenter] using hh
    have hLongU : κ ≤ ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) c u := by
      have hh := hLong N (by omega) X hNXL hXplus
      simpa only [hCenter] using hh
    have hAbs := neg_le_abs (G u)
    dsimp only [G] at hAbs
    change κ/2 ≤ |ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) b u-
      ActualGaussianMeanComparison.smoothed N (OrdinarySmoothIndicator.value Y) c u|
    linarith only [hAbs,hShortU,hLongU]
  have hXCells : ∀ j ∈ B, 0 < (j : ℝ)+shift := by
    intro j hj
    have hjBand := mem_Ico.mp (mem_filter.mp (mem_filter.mp hj).1).1
    have hjR : (N : ℝ) ≤ j := by exact_mod_cast hjBand.1
    dsimp only [shift]
    linarith only [hNP,hjR,hW6R]
  have hTopCells : ∀ j ∈ B, (j : ℝ)+shift+1 ≤ 4*(N : ℝ) := by
    intro j hj
    have hjBand := mem_Ico.mp (mem_filter.mp (mem_filter.mp hj).1).1
    have hjR : (j : ℝ) < 2*(N : ℝ) := by exact_mod_cast hjBand.2
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hNN
    dsimp only [shift]
    linarith only [hjR,hWNR,hNR]
  have hCell := LogarithmicCellSquareBudget.finite_budget B G hGI (κ/2) shift (4*(N : ℝ))
    (by positivity) hXCells hTopCells hCellGap
  have hB : (B.card : ℝ) ≤ τ*(N : ℝ)/2 := by
    have hQ : 0 < (κ/2)^2 := by positivity
    apply (mul_le_mul_iff_left₀ hQ).mp
    have hScaled := (div_le_iff₀ (by positivity : 0 < 4*(N : ℝ))).mp (hCell.trans hEnergy)
    calc
      _ ≤ (τ*(κ/2)^2/8)*(4*(N : ℝ)) := hScaled
      _ = _ := by ring
  have hBoundary : ((badWindows N Y).card : ℝ) ≤ (B.card : ℝ)+(windowLength N : ℝ) := by
    exact_mod_cast boundary_bound N Y hWN
  have hWindow : (windowLength N : ℝ) ≤ (τ/2)*(N : ℝ) :=
    (div_le_iff₀ hNP).mp (hWindowTail N (by omega)).le
  change ((badWindows N Y).card : ℝ) ≤ τ*(N : ℝ)
  linarith only [hBoundary,hB,hWindow]

end PaperP1.SmoothLogarithmicWindowDensity
