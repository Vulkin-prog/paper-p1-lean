module

public import PaperP1.Analysis.FullTriplePerron
public import PaperP1.Analysis.PrimeFactorCauchy
public import PaperP1.Analysis.ComplexEuler
public import PaperP1.Analysis.EulerFrequencyTruncation
public import PaperP1.Analysis.GaussianFrequencyTail
public import PaperP1.Analysis.LogarithmicGaussianTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ComplexEulerFrequencyTruncation
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem band_coefficient_norm (f : ℕ →* ℂ) (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    (X p : ℕ) (hp : p.Prime) (hXp : 2*p ≤ X) :
    ‖PrimeFactorCauchy.bandCoefficient f (X : ℝ) p‖ ≤ 1/Real.log 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hden : Real.log 2 ≤ Real.log ((X : ℝ)/(p : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast hXp
  have hden0 : 0 < Real.log ((X : ℝ)/(p : ℝ)) := htwo.trans_le hden
  simp only [PrimeFactorCauchy.bandCoefficient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hden0]
  calc
    _ ≤ 1/Real.log ((X : ℝ)/(p : ℝ)) := div_le_div_of_nonneg_right (hf p hp) hden0.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) htwo hden



def base (X : ℕ) (f : ℕ →* ℂ) (P Q : Finset ℕ) (t : ℝ) : ℝ :=
  ‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) t‖*
    ‖WeightedPrimeMean.value Q f t‖*
    ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖/Real.sqrt (1+t^2)

theorem base_continuous (X : ℕ) (f : ℕ →* ℂ) (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1) (P Q : Finset ℕ) :
    Continuous (base X f P Q) := by
  have hE := ComplexEuler.total_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X) f hf
  exact (((WeightedPrimeMean.value_continuous P _).norm.mul (WeightedPrimeMean.value_continuous Q _).norm).mul hE.norm).div
    (continuous_const.add (continuous_id.pow 2)).sqrt (fun t ↦ by positivity)

theorem base_nonneg (X : ℕ) (f : ℕ →* ℂ) (P Q : Finset ℕ) (t : ℝ) : 0 ≤ base X f P Q t := by
  dsimp only [base]
  positivity

theorem base_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ →* ℂ) (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ X) (t : ℝ) :
    base X f P Q t ≤ (FullEulerBound.eulerConstant/Real.log 2)*Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2 := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 ≤ Real.log 4+4 := by have hh := Real.log_natCast_nonneg 4; norm_num at hh; linarith
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hpm := EulerFrequencyTruncation.primeMass_bound X (by omega) P (by
    intro p hp
    exact ⟨(hP p hp).1,by have hh := (hP p hp).2; omega⟩)
    (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) (1/Real.log 2) (by positivity)
    (fun p hp ↦ band_coefficient_norm f hf X p (hP p hp).1 (hP p hp).2)
  have hqm : EulerIntegralLimit.primeMass Q f ≤ Real.log (X : ℝ)+(Real.log 4+4) := by
    have hh := EulerFrequencyTruncation.primeMass_bound X (by omega) Q hQ f 1 (by norm_num) (by
      intro q hq
      exact hf q (hQ q hq).1)
    simpa only [one_mul] using hh
  have hw :
      ‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) t‖*
      ‖WeightedPrimeMean.value Q f t‖/Real.sqrt (1+t^2) ≤
      EulerIntegralLimit.primeMass P (PrimeFactorCauchy.bandCoefficient f (X : ℝ))*
        EulerIntegralLimit.primeMass Q f := by
    have hh := EulerIntegralLimit.weight_bound 0 P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) Q f t
    simpa only [EulerIntegralLimit.weight,neg_zero,zero_mul,Real.exp_zero,one_mul,mul_one] using hh
  have he := ComplexEuler.total_global_bound X hX f hf t
  have hmass := mul_le_mul hpm hqm (EulerIntegralLimit.primeMass_nonneg Q _)
    (by positivity : 0 ≤ (1/Real.log 2)*(Real.log (X : ℝ)+(Real.log 4+4)))
  have hC : 0 ≤ FullEulerBound.eulerConstant*Real.log (X : ℝ) := mul_nonneg FullEulerBound.eulerConstant_pos.le hlog
  have hlast := mul_le_mul_of_nonneg_right hmass hC
  calc
    _ = (‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) t‖*
        ‖WeightedPrimeMean.value Q f t‖/Real.sqrt (1+t^2))*
        ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖ := by dsimp only [base]; ring
    _ ≤ (EulerIntegralLimit.primeMass P (PrimeFactorCauchy.bandCoefficient f (X : ℝ))*
        EulerIntegralLimit.primeMass Q f)*(FullEulerBound.eulerConstant*Real.log (X : ℝ)) :=
      mul_le_mul hw he (norm_nonneg _) (mul_nonneg (EulerIntegralLimit.primeMass_nonneg P _) (EulerIntegralLimit.primeMass_nonneg Q _))
    _ ≤ ((1/Real.log 2)*(Real.log (X : ℝ)+(Real.log 4+4))*(Real.log (X : ℝ)+(Real.log 4+4)))*
        (FullEulerBound.eulerConstant*Real.log (X : ℝ)) := hlast
    _ = _ := by ring



theorem whole_integral_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ →* ℂ) (hf : ∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ X) :
    (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
      (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) Q f t*
      ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖) ≤
      (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X, base X f P Q t)+EulerFrequencyTruncation.scaledTail X := by
  have hδ := LogarithmicGaussianSum.width_positive X hX
  have hh := GaussianFrequencyTail.whole_integral_bound ((LogarithmicGaussianSum.width X)^2)
    (LogarithmicGaussianTail.height X) (sq_pos_of_pos hδ) (LogarithmicGaussianTail.height_positive X hX).le
    (base X f P Q) (base_continuous X f hf P Q) (base_nonneg X f P Q)
    ((FullEulerBound.eulerConstant/Real.log 2)*Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2)
    (base_bound X hX f hf P Q hP hQ)
  have he : (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
      (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) Q f t*
      ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖)=
      ∫ t : ℝ, Real.exp (-((LogarithmicGaussianSum.width X)^2)*t^2)*base X f P Q t := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [EulerIntegralLimit.weight,base]
    ring
  rw [he]
  calc
    _ ≤ (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X, base X f P Q t)+
        ((FullEulerBound.eulerConstant/Real.log 2)*Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2)*
          GaussianFrequencyTail.tailBound ((LogarithmicGaussianSum.width X)^2) (LogarithmicGaussianTail.height X) := hh
    _ = _ := by dsimp only [EulerFrequencyTruncation.scaledTail,LogarithmicGaussianTail.tailEnvelope]; ring

theorem whole_integral_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℂ, (∀ p : ℕ, p.Prime → ‖f p‖ ≤ 1) →
      ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 2*p ≤ X) → (∀ q ∈ Q, q.Prime ∧ q ≤ X) →
      (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
        (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) Q f t*
        ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) f t‖) ≤
        (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X, base X f P Q t)+ε := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (EulerFrequencyTruncation.scaledTail_tendsto.eventually (eventually_lt_nhds hε))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX f hf P Q hP hQ
  exact (whole_integral_bound X (by omega) f hf P Q hP hQ).trans
    (add_le_add le_rfl (hX₀ X ((le_max_left _ _).trans hX)).le)
end PaperP1.ComplexEulerFrequencyTruncation
