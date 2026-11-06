module

public import PaperP1.Analysis.PrimeUnitMean
public import PaperP1.Analysis.PrimeLogDiameter
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Actual Cauchy-Schwarz prime factors and uniform logarithmic-band energies -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeFactorCauchy
open Finset MeasureTheory PaperP1 WeightedPrimeMean PrimeUnitMean
open scoped Classical

theorem interval_cauchy (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ t, 0 ≤ f t) (hg0 : ∀ t, 0 ≤ g t) (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in A..B, f t*g t) ≤ Real.sqrt (∫ t in A..B, (f t)^2)*Real.sqrt (∫ t in A..B, (g t)^2) := by
  have hfp : MemLp f 2 (volume.restrict (Set.Ioc A B)) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ((hf.pow 2).intervalIntegrable A B).1
  have hgp : MemLp g 2 (volume.restrict (Set.Ioc A B)) :=
    (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr ((hg.pow 2).intervalIntegrable A B).1
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict (Set.Ioc A B))
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa only [ENNReal.ofReal_ofNat] using hfp) (by simpa only [ENNReal.ofReal_ofNat] using hgp)
  simpa only [intervalIntegral.integral_of_le hAB,Real.rpow_two,Real.sqrt_eq_rpow] using hh

theorem prime_factor_integral_bound (P Q : Finset ℕ) (a b : ℕ → ℂ) (F : ℝ → ℂ)
    (hF : Continuous F) (K : ℕ) (T : ℝ) (hT : 1 ≤ T) (hTK : T ≤ (K : ℝ)+1/2)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ T^2 ≤ (p : ℝ)) (hQ : ∀ q ∈ Q, Nat.Prime q) :
    (∫ t in -T..T, ‖value P a t‖*‖value Q b t‖*‖F t‖/Real.sqrt (1+t^2)) ≤
      2*WeightedPrimeMean.constant*Real.sqrt (energy P a*energy Q b*frequencyBudget F K) := by
  let f : ℝ → ℝ := fun t ↦ ‖value P a t‖
  let g : ℝ → ℝ := fun t ↦ ‖value Q b t‖*‖F t‖/Real.sqrt (1+t^2)
  have hf : Continuous f := (value_continuous P a).norm
  have hg : Continuous g := by
    apply Continuous.div ((value_continuous Q b).norm.mul hF.norm)
      ((continuous_const.add (continuous_id.pow 2)).sqrt)
    intro t
    change Real.sqrt (1+t^2) ≠ 0
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hf0 (t : ℝ) : 0 ≤ f t := norm_nonneg _
  have hg0 (t : ℝ) : 0 ≤ g t := by dsimp only [g]; positivity
  have hh := interval_cauchy f g hf hg hf0 hg0 (-T) T (by linarith)
  have hgsq (t : ℝ) : (g t)^2=‖value Q b t‖^2*‖F t‖^2/(1+t^2) := by
    dsimp only [g]
    rw [div_pow,mul_pow,Real.sq_sqrt (by positivity)]
  have hprod (t : ℝ) : f t*g t=‖value P a t‖*‖value Q b t‖*‖F t‖/Real.sqrt (1+t^2) := by
    dsimp only [f,g]
    ring
  simp_rw [hprod,hgsq] at hh
  have h1 := WeightedPrimeMean.mean_square P a T hT hP
  have h2 := frequency_budget_mean Q b F hF K T (by linarith) hTK hQ
  have he1 := energy_nonneg P a
  have he2 := energy_nonneg Q b
  have hB := frequency_budget_nonneg F hF K
  have hC := WeightedPrimeMean.constant_pos
  have hright : Real.sqrt (WeightedPrimeMean.constant*energy P a)*
      Real.sqrt (2*WeightedPrimeMean.constant*energy Q b*frequencyBudget F K) ≤
      2*WeightedPrimeMean.constant*Real.sqrt (energy P a*energy Q b*frequencyBudget F K) := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hC.le he1),
      Real.sq_sqrt (by positivity : 0 ≤ 2*WeightedPrimeMean.constant*energy Q b*frequencyBudget F K),
      Real.sq_sqrt (by positivity : 0 ≤ energy P a*energy Q b*frequencyBudget F K)]
    have hn : 0 ≤ WeightedPrimeMean.constant^2*(energy P a*energy Q b*frequencyBudget F K) := by positivity
    nlinarith
  exact hh.trans ((mul_le_mul (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hright)

def bandCoefficient (a : ℕ → ℂ) (R : ℝ) (p : ℕ) : ℂ := a p/(Real.log (R/(p : ℝ)) : ℂ)

theorem energy_bound (P : Finset ℕ) (a : ℕ → ℂ) (B : ℝ)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ B) : energy P a ≤ B^2*PrimeLogDiameter.mass P := by
  calc
    _ ≤ ∑ p ∈ P, (Real.log (p : ℝ)/(p : ℝ))*B^2 := by
      apply sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (ha p hp) 2)
        (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    _ = _ := by rw [PrimeLogDiameter.mass,mul_sum]; apply sum_congr rfl; intro p hp; ring

theorem band_prime_mass (P : Finset ℕ) (R U : ℝ) (hR : 0 < R) (hU : 0 ≤ U)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ U ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ 2*U) :
    PrimeLogDiameter.mass P ≤ U+PrimeLogDiameter.constant := by
  apply PrimeLogDiameter.diameter_bound P U (fun p hp ↦ (hP p hp).1) hU
  intro p hp q hq
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hP p hp).1.ne_zero
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).1.ne_zero
  have hl := (hP p hp).2.1
  have hu := (hP q hq).2.2
  rw [Real.log_div hR.ne' hp0] at hl
  rw [Real.log_div hR.ne' hq0] at hu
  linarith

theorem band_energy (P : Finset ℕ) (a : ℕ → ℂ) (R U : ℝ) (hR : 0 < R) (hU : 0 < U)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ U ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ 2*U) :
    energy P (bandCoefficient a R) ≤ (U+PrimeLogDiameter.constant)/U^2 := by
  have hb : ∀ p ∈ P, ‖bandCoefficient a R p‖ ≤ 1/U := by
    intro p hp
    have hl : 0 < Real.log (R/(p : ℝ)) := lt_of_lt_of_le hU (hP p hp).2.1
    rw [bandCoefficient,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hl]
    exact (div_le_div_of_nonneg_right (ha p hp) hl.le).trans
      (div_le_div_of_nonneg_left (by norm_num) hU (hP p hp).2.1)
  calc
    _ ≤ (1/U)^2*PrimeLogDiameter.mass P := energy_bound P _ _ hb
    _ ≤ (1/U)^2*(U+PrimeLogDiameter.constant) :=
      mul_le_mul_of_nonneg_left (band_prime_mass P R U hR hU.le hP) (sq_nonneg _)
    _ = _ := by ring

theorem second_energy (Q : Finset ℕ) (b : ℕ → ℂ) (U : ℝ) (hU : 0 ≤ U)
    (hb : ∀ q ∈ Q, ‖b q‖ ≤ 1) (hQ : ∀ q ∈ Q, Nat.Prime q ∧ Real.log (q : ℝ) ≤ 2*U) :
    energy Q b ≤ 2*U+PrimeLogDiameter.constant := by
  have he := energy_bound Q b 1 hb
  norm_num only [one_pow,one_mul] at he
  exact he.trans (PrimeLogDiameter.diameter_bound Q (2*U) (fun q hq ↦ (hQ q hq).1) (by positivity) (by
    intro p hp q hq
    linarith [(hQ p hp).2,Real.log_natCast_nonneg q]))

theorem band_energy_product (P Q : Finset ℕ) (a b : ℕ → ℂ) (R U : ℝ)
    (hR : 0 < R) (hU : Real.log 2 ≤ U)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ q ∈ Q, ‖b q‖ ≤ 1)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ U ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ 2*U)
    (hQ : ∀ q ∈ Q, Nat.Prime q ∧ Real.log (q : ℝ) ≤ 2*U) :
    energy P (bandCoefficient a R)*energy Q b ≤
      (2+PrimeLogDiameter.constant/Real.log 2)^2 := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hU0 : 0 < U := lt_of_lt_of_le htwo hU
  have hC := PrimeLogDiameter.constant_pos
  have hdiv : PrimeLogDiameter.constant/U ≤ PrimeLogDiameter.constant/Real.log 2 :=
    div_le_div_of_nonneg_left hC.le htwo hU
  calc
    _ ≤ ((U+PrimeLogDiameter.constant)/U^2)*(2*U+PrimeLogDiameter.constant) :=
      mul_le_mul (band_energy P a R U hR hU0 ha hP) (second_energy Q b U hU0.le hb hQ)
        (energy_nonneg Q b) (by positivity)
    _ = (1+PrimeLogDiameter.constant/U)*(2+PrimeLogDiameter.constant/U) := by field_simp
    _ ≤ (2+PrimeLogDiameter.constant/Real.log 2)*(2+PrimeLogDiameter.constant/Real.log 2) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = _ := by ring

def bandConstant : ℝ := 2*WeightedPrimeMean.constant*(2+PrimeLogDiameter.constant/Real.log 2)

theorem bandConstant_pos : 0 < bandConstant := by
  have hc := WeightedPrimeMean.constant_pos
  have hd := PrimeLogDiameter.constant_pos
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  dsimp only [bandConstant]
  positivity

theorem band_factor_integral_bound (P Q : Finset ℕ) (a b : ℕ → ℂ) (F : ℝ → ℂ)
    (hF : Continuous F) (R U : ℝ) (hR : 0 < R) (hU : Real.log 2 ≤ U)
    (K : ℕ) (T : ℝ) (hT : 1 ≤ T) (hTK : T ≤ (K : ℝ)+1/2)
    (ha : ∀ p ∈ P, ‖a p‖ ≤ 1) (hb : ∀ q ∈ Q, ‖b q‖ ≤ 1)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ T^2 ≤ (p : ℝ) ∧ U ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ 2*U)
    (hQ : ∀ q ∈ Q, Nat.Prime q ∧ Real.log (q : ℝ) ≤ 2*U) :
    (∫ t in -T..T, ‖value P (bandCoefficient a R) t‖*‖value Q b t‖*‖F t‖/Real.sqrt (1+t^2)) ≤
      bandConstant*Real.sqrt (frequencyBudget F K) := by
  have hh := prime_factor_integral_bound P Q (bandCoefficient a R) b F hF K T hT hTK
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩) (fun q hq ↦ (hQ q hq).1)
  have he := band_energy_product P Q a b R U hR hU ha hb
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩) hQ
  have hB := frequency_budget_nonneg F hF K
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 ≤ 2+PrimeLogDiameter.constant/Real.log 2 := by
    have hc := PrimeLogDiameter.constant_pos
    positivity
  have hr : Real.sqrt (energy P (bandCoefficient a R)*energy Q b*frequencyBudget F K) ≤
      (2+PrimeLogDiameter.constant/Real.log 2)*Real.sqrt (frequencyBudget F K) := by
    calc
      _ ≤ Real.sqrt ((2+PrimeLogDiameter.constant/Real.log 2)^2*frequencyBudget F K) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right he hB)
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hD]
  calc
    _ ≤ 2*WeightedPrimeMean.constant*
        Real.sqrt (energy P (bandCoefficient a R)*energy Q b*frequencyBudget F K) := hh
    _ ≤ 2*WeightedPrimeMean.constant*((2+PrimeLogDiameter.constant/Real.log 2)*Real.sqrt (frequencyBudget F K)) :=
      mul_le_mul_of_nonneg_left hr (by have hc := WeightedPrimeMean.constant_pos; positivity)
    _ = _ := by dsimp only [bandConstant]; ring
end PaperP1.PrimeFactorCauchy


