module

public import PaperP1.Analysis.GaussianEnergyReduction
public import PaperP1.Analysis.ScaledRealOffCentralEnergy
public import PaperP1.Analysis.GaussianLogarithmicScales


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformGaussianFrequencyEnergy
open Finset Filter MeasureTheory PaperP1 GaussianLogarithmicScales
open scoped Classical

theorem dyadic_uniform_bound (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ M : ℕ, N ≤ M → M ≤ 2*N → ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∫ t : ℝ, GaussianDifferenceWeights.weight (shortWidth D N) (longWidth N) t*
        ‖DirichletPolynomialMeanValue.value (Ico M (2*M)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  have hK : 0 < uniformBudget := by unfold uniformBudget; positivity
  have hExpLimit : Tendsto (fun L : ℝ ↦ Real.exp (-L)*uniformBudget) atTop (nhds 0) := by
    simpa only [zero_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const uniformBudget
  obtain ⟨LE,hExpTail⟩ := eventually_atTop.mp
    (hExpLimit.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<ε/3)))
  let L : ℝ := max 1 LE
  have hL : 1 ≤ L := le_max_left _ _
  have hLP : 0 < L := by linarith only [hL]
  have hExp : Real.exp (-L)*uniformBudget ≤ ε/3 := (hExpTail L (le_max_right _ _)).le
  obtain ⟨R,hR,hFrequency⟩ := ScaledRealOffCentralEnergy.common_central_bound (ε/3) (by positivity)
  obtain ⟨NF,hNF,hFreq⟩ := hFrequency (2*D*Real.sqrt L) (by positivity)
  obtain ⟨NC,hCentral⟩ := eventually_atTop.mp
    ((central_error_tendsto D R).eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<ε/3)))
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NB,hLogTail⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop D))
  obtain ⟨NO,hOrder⟩ := eventually_atTop.mp (eventual_order D hD)
  obtain ⟨NH,hHeight⟩ := eventually_atTop.mp
    ((height_tendsto D L hD hLP).eventually (eventually_ge_atTop (max 1 R)))
  refine ⟨max 2 (max NF (max NC (max NB (max NO NH)))),by omega,?_⟩
  intro N hN M hNM hMN f hf
  have hNN : 2 ≤ N := by omega
  have hPos : 0 < N := by omega
  have hb : 0 < shortWidth D N := shortWidth_pos D hD N hNN
  have hbc : shortWidth D N ≤ longWidth N := hOrder N (by omega)
  have hTR : R ≤ height D L N := (le_max_right _ _).trans (hHeight N (by omega))
  have hT1 : 1 ≤ height D L N := (le_max_left _ _).trans (hHeight N (by omega))
  have hCoef : ∀ n ∈ Ico M (2*M), ‖(f n : ℂ)‖ ≤ 1 := by
    intro n hn
    have hn0 : n≠0 := by have hh := (mem_Ico.mp hn).1; omega
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      FinitePrimeDirichletTruncation.real_hom_bound f hf n hn0
  have hReduction := GaussianEnergyReduction.quantitative_bound M (by omega) (Ico M (2*M))
    (Subset.rfl) (fun n ↦ (f n : ℂ)) hCoef (shortWidth D N) (longWidth N) R (height D L N)
    hb hbc (by linarith only [hR]) hTR
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by exact_mod_cast hPos
  have hLogN : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hMR : 1 < (M : ℝ) := by exact_mod_cast (by omega : 1<M)
  have hMP : 0 < (M : ℝ) := by linarith only [hMR]
  have hLogM : 0 < Real.log (M : ℝ) := Real.log_pos hMR
  have hNMR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
  have hLog2 : Real.log (M : ℝ) ≤ 2*Real.log (N : ℝ) := by
    have hTop : (M : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hMN
    have hLogTop := Real.log_le_log hMP hTop
    have hLogTwo : Real.log 2 ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hNN)
    rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) hNP.ne'] at hLogTop
    linarith only [hLogTop,hLogTwo]
  have hRatio : (N : ℝ)/Real.log (N : ℝ) ≤ 2*(M : ℝ)/Real.log (M : ℝ) := by
    apply (div_le_div_iff₀ hLogN hLogM).mpr
    exact (mul_le_mul_of_nonneg_left hLog2 hNP.le).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right hNMR hLogN.le])
  have hTime : height D L N ≤ (2*D*Real.sqrt L)*(M : ℝ)/Real.log (M : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hRatio (by positivity : 0 ≤ D*Real.sqrt L)
    calc
      _ = D*Real.sqrt L*((N : ℝ)/Real.log (N : ℝ)) := by unfold height; ring
      _ ≤ D*Real.sqrt L*(2*(M : ℝ)/Real.log (M : ℝ)) := hh
      _ = _ := by ring
  have hMid := hFreq M (by omega) f hf (height D L N) hT1 hTime
  have hCentralBound : 2*(shortWidth D N+longWidth N)^2*R^5 ≤ ε/3 := (hCentral N (by omega)).le
  have hBudgetN := budget_bound D hD N hNN (hLogTail N (by omega))
  have hBudget : GaussianDirichletTail.budget M (shortWidth D N) ≤ uniformBudget := by
    have hh := div_le_div_of_nonneg_left (Real.sqrt_nonneg (Real.pi/shortWidth D N)) hNP hNMR
    exact (add_le_add hh le_rfl).trans hBudgetN
  have hTail : Real.exp (-(shortWidth D N)*(height D L N)^2)*
      GaussianDirichletTail.budget M (shortWidth D N) ≤ ε/3 := by
    rw [neg_mul,height_product D L hD hLP.le N hNN]
    exact (mul_le_mul_of_nonneg_left hBudget (Real.exp_pos _).le).trans hExp
  linarith only [hReduction,hMid,hCentralBound,hTail]

theorem uniform_bound (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∫ t : ℝ, GaussianDifferenceWeights.weight (shortWidth D N) (longWidth N) t*
        ‖DirichletPolynomialMeanValue.value (Ico N (2*N)) (fun n ↦ (f n : ℂ)) t‖^2) ≤ ε := by
  obtain ⟨N₀,hN₀,hBound⟩ := dyadic_uniform_bound D hD ε hε
  exact ⟨N₀,hN₀,fun N hN f hf ↦ hBound N hN N le_rfl (by omega) f hf⟩

end PaperP1.UniformGaussianFrequencyEnergy
