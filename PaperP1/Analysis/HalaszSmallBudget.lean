module

public import PaperP1.Arithmetic.PrimeTruncation
public import PaperP1.Analysis.ActualEulerBand
public import PaperP1.Analysis.ComplexEuler
public import PaperP1.Analysis.GlobalTripleBand
public import PaperP1.Analysis.TrivialTripleBand
public import PaperP1.Analysis.WeightedPerronError

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.HalaszSmallBudget
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem summatory_small_of_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ g : ℕ →* ℂ,
      (∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) →
      GlobalTripleBand.budget X g ≤ η*(Real.log (X : ℝ))^2 →
      ‖MultiplicativeLogConvolution.summatory g X‖ ≤ ε*(X : ℝ) := by
  have hCt := TrivialTripleBand.constant_pos
  have hCa := ActualEulerBand.constant_pos
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt (16*TrivialTripleBand.constant/ε) (by norm_num : (1 : ℝ) < 2)
  let m : ℕ := n+1
  have hm : 0 < m := by dsimp only [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsmall : 4*TrivialTripleBand.constant/(2 : ℝ)^m ≤ ε/4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^m)).mpr
    have hnr := (div_lt_iff₀ hε).mp hn
    dsimp only [m]
    rw [pow_succ]
    nlinarith
  let η : ℝ := (ε/(4*(m : ℝ)*ActualEulerBand.constant))^2
  let δ : ℝ := ε/(4*(m : ℝ))
  have hη : 0 < η := by dsimp only [η]; positivity
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hsqrt : Real.sqrt η=ε/(4*(m : ℝ)*ActualEulerBand.constant) := by
    dsimp only [η]
    exact Real.sqrt_sq (by positivity)
  have hηcancel : (m : ℝ)*ActualEulerBand.constant*Real.sqrt η=ε/4 := by
    rw [hsqrt]
    field_simp [hmR.ne',hCa.ne']
  have hδcancel : (m : ℝ)*δ=ε/4 := by dsimp only [δ]; field_simp [hmR.ne']
  obtain ⟨X₁,hX₁,hglobal⟩ := GlobalTripleBand.global_triple_bound
  obtain ⟨X₂,hX₂,hrecon⟩ := PrimeTruncation.total_triple_small_uniform 20 (ε/4) (by positivity)
  obtain ⟨X₃,hX₃,hweight⟩ := WeightedPerronError.weightedNormalized_small δ hδ
  have hloglim : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨X₄,hX₄⟩ := eventually_atTop.mp (hloglim.eventually (eventually_ge_atTop 1))
  refine ⟨η,hη,max (max X₁ X₂) (max X₃ (max X₄ 4)),by omega,?_⟩
  intro X hX g hg hbudget
  let L := Real.log (X : ℝ)
  let E := WeightedPerronError.combinedError X
  let P := PrimeTruncation.retained X (PrimeTruncation.cutoff 20 X)
  have hL : 1 ≤ L := hX₄ X (by omega)
  have hLP : 0 < L := by linarith
  have hXP : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hEnn : 0 ≤ E := WeightedPerronError.combinedError_nonneg X
  have hw := hweight X (by omega)
  change (L^2/(X : ℝ))*E ≤ δ at hw
  have hmul := mul_le_mul_of_nonneg_right hw hXP.le
  have heq : ((L^2/(X : ℝ))*E)*(X : ℝ)=L^2*E := by field_simp [hXP.ne']
  rw [heq] at hmul
  have hEle : E ≤ δ*(X : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ L^2 by nlinarith) hEnn
    exact (by simpa only [one_mul] using hh : E ≤ L^2*E).trans hmul
  have herror : (m : ℝ)*E/L ≤ (ε/4)*(X : ℝ) := by
    calc
      _ = (m : ℝ)*(E/L) := by ring
      _ ≤ (m : ℝ)*(δ*(X : ℝ)) := mul_le_mul_of_nonneg_left ((div_le_self hEnn hL).trans hEle) hmR.le
      _ = ((m : ℝ)*δ)*(X : ℝ) := by ring
      _ = _ := by rw [hδcancel]
  have hroot : Real.sqrt (GlobalTripleBand.budget X g) ≤ Real.sqrt η*L := by
    calc
      _ ≤ Real.sqrt (η*L^2) := Real.sqrt_le_sqrt hbudget
      _ = _ := by rw [Real.sqrt_mul hη.le,Real.sqrt_sq hLP.le]
  have hrootmul := mul_le_mul_of_nonneg_left hroot (mul_nonneg hCa.le hXP.le)
  have ht := (hglobal X (by omega) g hg m).trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (add_le_add hrootmul le_rfl) hmR.le))
  have hmain : ‖RealTripleConvolution.triple g X P‖/L ≤
      (4*TrivialTripleBand.constant/(2 : ℝ)^m+(m : ℝ)*ActualEulerBand.constant*Real.sqrt η)*(X : ℝ)+(m : ℝ)*E/L := by
    calc
      _ ≤ (TrivialTripleBand.constant*(X : ℝ)*(4*L/(2 : ℝ)^m)+
          (m : ℝ)*(ActualEulerBand.constant*(X : ℝ)*(Real.sqrt η*L)+E))/L :=
        div_le_div_of_nonneg_right ht hLP.le
      _ = _ := by field_simp [hLP.ne']; ring
  have hcoeff : 4*TrivialTripleBand.constant/(2 : ℝ)^m+(m : ℝ)*ActualEulerBand.constant*Real.sqrt η ≤ ε/2 := by
    rw [hηcancel]
    linarith
  have htriple : ‖RealTripleConvolution.triple g X P‖/L ≤ (3*ε/4)*(X : ℝ) := by
    calc
      _ ≤ (4*TrivialTripleBand.constant/(2 : ℝ)^m+(m : ℝ)*ActualEulerBand.constant*Real.sqrt η)*(X : ℝ)+(m : ℝ)*E/L := hmain
      _ ≤ (ε/2)*(X : ℝ)+(ε/4)*(X : ℝ) := add_le_add (mul_le_mul_of_nonneg_right hcoeff hXP.le) herror
      _ = _ := by ring
  have hr := hrecon X (by omega) g (fun n hn ↦ ComplexEuler.complex_hom_bound g hg n hn.ne')
  have hquot : ‖RealTripleConvolution.triple g X P/(L : ℂ)‖=‖RealTripleConvolution.triple g X P‖/L := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLP]
  have htriangle : ‖MultiplicativeLogConvolution.summatory g X‖ ≤ ‖RealTripleConvolution.triple g X P/(L : ℂ)‖+
      ‖MultiplicativeLogConvolution.summatory g X-RealTripleConvolution.triple g X P/(L : ℂ)‖ := by
    calc
      _ = ‖RealTripleConvolution.triple g X P/(L : ℂ)+
          (MultiplicativeLogConvolution.summatory g X-RealTripleConvolution.triple g X P/(L : ℂ))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [hquot] at htriangle
  have hfinal := htriangle.trans (add_le_add htriple hr)
  nlinarith
end PaperP1.HalaszSmallBudget
