module

public import PaperP1.Analysis.FullEulerBound
public import PaperP1.Analysis.FullTriplePerron
public import PaperP1.Analysis.PrimeFactorCauchy
public import PaperP1.Analysis.GaussianFrequencyTail
public import PaperP1.Analysis.LogarithmicGaussianTail

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.EulerFrequencyTruncation
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

theorem prime_mass_identity (X : ℕ) : PrimeLogDiameter.mass (FixedEulerTruncation.primes X)=PrimeLogMertens.weightedPrimes X := by
  have hh := PrimeLogDiameter.interval_identity 0 X (Nat.zero_le X)
  have hset : (Ioc 0 X).filter Nat.Prime=FixedEulerTruncation.primes X := by
    ext p
    simp only [FixedEulerTruncation.primes,mem_filter,mem_Ioc,mem_Icc]
    constructor
    · rintro ⟨hp,hprime⟩
      exact ⟨⟨by omega,hp.2⟩,hprime⟩
    · rintro ⟨hp,hprime⟩
      exact ⟨⟨by omega,hp.2⟩,hprime⟩
  have hzero : PrimeLogMertens.weightedPrimes 0=0 := by norm_num [PrimeLogMertens.weightedPrimes,PrimeLogMertens.coefficient]
  simpa only [hset,hzero,sub_zero] using hh

theorem prime_mass_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) :
    PrimeLogDiameter.mass P ≤ Real.log (X : ℝ)+(Real.log 4+4) := by
  have hsub : P ⊆ FixedEulerTruncation.primes X := by
    intro p hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(hP p hp).1.one_le,(hP p hp).2⟩,(hP p hp).1⟩
  calc
    _ ≤ PrimeLogDiameter.mass (FixedEulerTruncation.primes X) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ ↦ div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ = _ := prime_mass_identity X
    _ ≤ _ := (PrimeLogMertens.natural_bounds X hX).2

theorem primeMass_bound (X : ℕ) (hX : 1 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ X) (a : ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ B) :
    EulerIntegralLimit.primeMass P a ≤ B*(Real.log (X : ℝ)+(Real.log 4+4)) := by
  calc
    _ ≤ ∑ p ∈ P, (Real.log (p : ℝ)/(p : ℝ))*B :=
      sum_le_sum (fun p hp ↦ mul_le_mul_of_nonneg_left (ha p hp) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)))
    _ = B*PrimeLogDiameter.mass P := by rw [PrimeLogDiameter.mass,mul_sum]; apply sum_congr rfl; intro p hp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (prime_mass_bound X hX P hP) hB

theorem band_coefficient_norm (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (X p : ℕ) (hp : p.Prime) (hXp : 2*p ≤ X) :
    ‖PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ) p‖ ≤ 1/Real.log 2 := by
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



def base (X : ℕ) (f : ℕ → ℝ) (P Q : Finset ℕ) (t : ℝ) : ℝ :=
  ‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) t‖*
    ‖WeightedPrimeMean.value Q (fun n ↦ (f n : ℂ)) t‖*
    ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖/Real.sqrt (1+t^2)

theorem base_continuous (X : ℕ) (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (P Q : Finset ℕ) :
    Continuous (base X f P Q) := by
  have hE := RealPrimeEulerBound.product_continuous (FixedEulerTruncation.primes X) (FixedEulerTruncation.primes_prime X)
    f (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp))
  exact (((WeightedPrimeMean.value_continuous P _).norm.mul (WeightedPrimeMean.value_continuous Q _).norm).mul hE.norm).div
    (continuous_const.add (continuous_id.pow 2)).sqrt (fun t ↦ by positivity)

theorem base_nonneg (X : ℕ) (f : ℕ → ℝ) (P Q : Finset ℕ) (t : ℝ) : 0 ≤ base X f P Q t := by
  dsimp only [base]
  positivity

theorem base_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ X) (t : ℝ) :
    base X f P Q t ≤ (FullEulerBound.eulerConstant/Real.log 2)*Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2 := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB : 0 ≤ Real.log 4+4 := by have hh := Real.log_natCast_nonneg 4; norm_num at hh; linarith
  have hlog : 0 ≤ Real.log (X : ℝ) := Real.log_natCast_nonneg X
  have hpm := primeMass_bound X (by omega) P (by
    intro p hp
    exact ⟨(hP p hp).1,by have hh := (hP p hp).2; omega⟩)
    (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) (1/Real.log 2) (by positivity)
    (fun p hp ↦ band_coefficient_norm f hf X p (hP p hp).1 (hP p hp).2)
  have hqm : EulerIntegralLimit.primeMass Q (fun n ↦ (f n : ℂ)) ≤ Real.log (X : ℝ)+(Real.log 4+4) := by
    have hh := primeMass_bound X (by omega) Q hQ (fun n ↦ (f n : ℂ)) 1 (by norm_num) (by
      intro q hq
      simpa only [Complex.norm_real,Real.norm_eq_abs] using hf q (hQ q hq).1)
    simpa only [one_mul] using hh
  have hw :
      ‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) t‖*
      ‖WeightedPrimeMean.value Q (fun n ↦ (f n : ℂ)) t‖/Real.sqrt (1+t^2) ≤
      EulerIntegralLimit.primeMass P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ))*
        EulerIntegralLimit.primeMass Q (fun n ↦ (f n : ℂ)) := by
    have hh := EulerIntegralLimit.weight_bound 0 P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) Q (fun n ↦ (f n : ℂ)) t
    simpa only [EulerIntegralLimit.weight,neg_zero,zero_mul,Real.exp_zero,one_mul,mul_one] using hh
  have he := FullEulerBound.global_bound X hX f hf t
  have hmass := mul_le_mul hpm hqm (EulerIntegralLimit.primeMass_nonneg Q _)
    (by positivity : 0 ≤ (1/Real.log 2)*(Real.log (X : ℝ)+(Real.log 4+4)))
  have hC : 0 ≤ FullEulerBound.eulerConstant*Real.log (X : ℝ) := mul_nonneg FullEulerBound.eulerConstant_pos.le hlog
  have hlast := mul_le_mul_of_nonneg_right hmass hC
  calc
    _ = (‖WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) t‖*
        ‖WeightedPrimeMean.value Q (fun n ↦ (f n : ℂ)) t‖/Real.sqrt (1+t^2))*
        ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖ := by dsimp only [base]; ring
    _ ≤ (EulerIntegralLimit.primeMass P (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ))*
        EulerIntegralLimit.primeMass Q (fun n ↦ (f n : ℂ)))*(FullEulerBound.eulerConstant*Real.log (X : ℝ)) :=
      mul_le_mul hw he (norm_nonneg _) (mul_nonneg (EulerIntegralLimit.primeMass_nonneg P _) (EulerIntegralLimit.primeMass_nonneg Q _))
    _ ≤ ((1/Real.log 2)*(Real.log (X : ℝ)+(Real.log 4+4))*(Real.log (X : ℝ)+(Real.log 4+4)))*
        (FullEulerBound.eulerConstant*Real.log (X : ℝ)) := hlast
    _ = _ := by ring


def scaledTail (X : ℕ) : ℝ := (FullEulerBound.eulerConstant/Real.log 2)*LogarithmicGaussianTail.tailEnvelope X

theorem scaledTail_nonneg (X : ℕ) : 0 ≤ scaledTail X := by
  have hC := FullEulerBound.eulerConstant_pos
  dsimp only [scaledTail]
  exact mul_nonneg (by positivity) (LogarithmicGaussianTail.tailEnvelope_nonneg X)

theorem scaledTail_tendsto : Tendsto scaledTail atTop (nhds 0) := by
  change Tendsto (fun X : ℕ ↦ (FullEulerBound.eulerConstant/Real.log 2)*LogarithmicGaussianTail.tailEnvelope X) atTop (nhds 0)
  simpa only [mul_zero] using
    LogarithmicGaussianTail.tailEnvelope_tendsto.const_mul (FullEulerBound.eulerConstant/Real.log 2)

theorem whole_integral_bound (X : ℕ) (hX : 2 ≤ X) (f : ℕ → ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ X) :
    (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
      (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) Q (fun n ↦ (f n : ℂ)) t*
      ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖) ≤
      (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X, base X f P Q t)+scaledTail X := by
  have hδ := LogarithmicGaussianSum.width_positive X hX
  have hh := GaussianFrequencyTail.whole_integral_bound ((LogarithmicGaussianSum.width X)^2)
    (LogarithmicGaussianTail.height X) (sq_pos_of_pos hδ) (LogarithmicGaussianTail.height_positive X hX).le
    (base X f P Q) (base_continuous X f hf P Q) (base_nonneg X f P Q)
    ((FullEulerBound.eulerConstant/Real.log 2)*Real.log (X : ℝ)*(Real.log (X : ℝ)+(Real.log 4+4))^2)
    (base_bound X hX f hf P Q hP hQ)
  have he : (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
      (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) Q (fun n ↦ (f n : ℂ)) t*
      ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖)=
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
    _ = _ := by dsimp only [scaledTail,LogarithmicGaussianTail.tailEnvelope]; ring

theorem whole_integral_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ → ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ P Q : Finset ℕ, (∀ p ∈ P, p.Prime ∧ 2*p ≤ X) → (∀ q ∈ Q, q.Prime ∧ q ≤ X) →
      (∫ t : ℝ, EulerIntegralLimit.weight ((LogarithmicGaussianSum.width X)^2) P
        (PrimeFactorCauchy.bandCoefficient (fun n ↦ (f n : ℂ)) (X : ℝ)) Q (fun n ↦ (f n : ℂ)) t*
        ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f t‖) ≤
        (∫ t in -(LogarithmicGaussianTail.height X)..LogarithmicGaussianTail.height X, base X f P Q t)+ε := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (scaledTail_tendsto.eventually (eventually_lt_nhds hε))
  refine ⟨max X₀ 2,le_max_right _ _,?_⟩
  intro X hX f hf P Q hP hQ
  exact (whole_integral_bound X (by omega) f hf P Q hP hQ).trans
    (add_le_add le_rfl (hX₀ X ((le_max_left _ _).trans hX)).le)
end PaperP1.EulerFrequencyTruncation
