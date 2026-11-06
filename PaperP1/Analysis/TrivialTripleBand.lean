module

public import PaperP1.Arithmetic.PrimeTruncation
public import PaperP1.Analysis.PrimeFactorCauchy
public import PaperP1.Analysis.ComplexEuler

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TrivialTripleBand
open Finset Nat MeasureTheory PaperP1 Filter
open scoped Classical

def constant : ℝ := (1+PrimeLogDiameter.constant/Real.log 2)*
  (1+(1+PrimeLogMertens.primePowerTotal)/Real.log 2)

theorem constant_pos : 0 < constant := by
  have hC := PrimeLogDiameter.constant_pos
  have hP := PrimeLogMertens.primePowerTotal_nonneg
  have ht : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  dsimp only [constant]
  positivity

theorem restricted_norm (g : ℕ →* ℂ) (hg : ∀ n : ℕ, 0 < n → ‖g n‖ ≤ 1)
    (X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ‖RealTripleConvolution.restricted g X P‖ ≤ (X : ℝ)*PrimeLogDiameter.mass P := by
  calc
    _ ≤ ∑ p ∈ P, ‖PrimeTruncation.term g X p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) :=
      sum_le_sum (fun p hp ↦ PrimeTruncation.term_reciprocal_bound g hg X p (hP p hp))
    _ = _ := by rw [PrimeLogDiameter.mass,mul_sum]

theorem reciprocal_weight_bound (X : ℕ) (U : ℝ) (hU : 0 < U) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ U ≤ Real.log ((X : ℝ)/(p : ℝ))) :
    RealTripleConvolution.reciprocalWeight X P ≤ PrimeLogDiameter.mass P/U := by
  have hpoint (p : ℕ) (hp : p ∈ P) :
      Real.log (p : ℝ)/((p : ℝ)*Real.log ((X : ℝ)/(p : ℝ))) ≤ (1/U)*(Real.log (p : ℝ)/(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    calc
      _ ≤ Real.log (p : ℝ)/((p : ℝ)*U) :=
        div_le_div_of_nonneg_left (Real.log_natCast_nonneg p) (mul_pos hpR hU)
          (mul_le_mul_of_nonneg_left (hP p hp).2 hpR.le)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  calc
    _ ≤ ∑ p ∈ P, (1/U)*(Real.log (p : ℝ)/(p : ℝ)) := sum_le_sum hpoint
    _ = (1/U)*PrimeLogDiameter.mass P := by rw [PrimeLogDiameter.mass,mul_sum]
    _ = _ := by ring


theorem band_norm_bound (X : ℕ) (hX : 2 ≤ X) (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1)
    (U : ℝ) (hU : Real.log 2 ≤ U) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X ∧ U ≤ Real.log ((X : ℝ)/(p : ℝ)) ∧ Real.log ((X : ℝ)/(p : ℝ)) ≤ 2*U) :
    ‖RealTripleConvolution.triple g X P‖ ≤ constant*(X : ℝ)*U := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hU0 : 0 < U := htwo.trans_le hU
  have hD := PrimeLogDiameter.constant_pos
  have hPtotal := PrimeLogMertens.primePowerTotal_nonneg
  have hunit : ∀ n : ℕ, 0 < n → ‖g n‖ ≤ 1 := fun n hn ↦ ComplexEuler.complex_hom_bound g hg n hn.ne'
  have hr := restricted_norm g hunit X P (fun p hp ↦ (hP p hp).1)
  have he := RealTripleConvolution.triple_error g hunit X P (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.1⟩)
  have hw := reciprocal_weight_bound X U hU0 P (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2.1⟩)
  have hm := PrimeFactorCauchy.band_prime_mass P (X : ℝ) U (by exact_mod_cast (by omega : 0 < X)) hU0.le
    (fun p hp ↦ ⟨(hP p hp).1,(hP p hp).2.2⟩)
  have hcU : 0 ≤ (1+PrimeLogMertens.primePowerTotal)*(X : ℝ) := by positivity
  have htri : ‖RealTripleConvolution.triple g X P‖ ≤
      ‖RealTripleConvolution.restricted g X P‖+‖RealTripleConvolution.restricted g X P-RealTripleConvolution.triple g X P‖ := by
    calc
      _ = ‖RealTripleConvolution.restricted g X P-
          (RealTripleConvolution.restricted g X P-RealTripleConvolution.triple g X P)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hstart := htri.trans (add_le_add hr (he.trans (mul_le_mul_of_nonneg_left hw hcU)))
  have hmass : (X : ℝ)*(1+(1+PrimeLogMertens.primePowerTotal)/U)*PrimeLogDiameter.mass P ≤
      (X : ℝ)*(1+(1+PrimeLogMertens.primePowerTotal)/U)*(U+PrimeLogDiameter.constant) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hprod := mul_le_mul
    (add_le_add le_rfl (div_le_div_of_nonneg_left (by positivity : 0 ≤ 1+PrimeLogMertens.primePowerTotal) htwo hU))
    (add_le_add le_rfl (div_le_div_of_nonneg_left hD.le htwo hU))
    (by positivity : 0 ≤ 1+PrimeLogDiameter.constant/U)
    (by positivity : 0 ≤ 1+(1+PrimeLogMertens.primePowerTotal)/Real.log 2)
  have hlast := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (X : ℝ)*U by positivity)
  calc
    _ ≤ (X : ℝ)*PrimeLogDiameter.mass P+(1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*(PrimeLogDiameter.mass P/U) := hstart
    _ = (X : ℝ)*(1+(1+PrimeLogMertens.primePowerTotal)/U)*PrimeLogDiameter.mass P := by ring
    _ ≤ (X : ℝ)*(1+(1+PrimeLogMertens.primePowerTotal)/U)*(U+PrimeLogDiameter.constant) := hmass
    _ = ((X : ℝ)*U)*((1+(1+PrimeLogMertens.primePowerTotal)/U)*(1+PrimeLogDiameter.constant/U)) := by field_simp [hU0.ne']
    _ ≤ ((X : ℝ)*U)*((1+(1+PrimeLogMertens.primePowerTotal)/Real.log 2)*(1+PrimeLogDiameter.constant/Real.log 2)) := hlast
    _ = _ := by dsimp only [constant]; ring
end PaperP1.TrivialTripleBand
