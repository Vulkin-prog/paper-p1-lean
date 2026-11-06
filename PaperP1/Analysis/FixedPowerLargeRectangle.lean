module

public import PaperP1.Analysis.UniformActualNarrowCofactor
public import PaperP1.Analysis.FiniteProductSampleBound
public import PaperP1.Analysis.FixedWidthLargeFrequencyCardinality
public import PaperP1.Analysis.FixedPowerPrimeSamples


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerLargeRectangle
open Finset Filter PaperP1
open scoped Classical

def constant (a : ℝ) (H : ℕ) : ℝ := ((H : ℝ)+1)^2*FixedPowerPrimeSamples.constant a

theorem constant_pos (a : ℝ) (H : ℕ) (ha : 0 < a) : 0 < constant a H := by
  have hh := FixedPowerPrimeSamples.constant_pos a ha
  unfold constant
  positivity

theorem uniform_bound {ι : Type*} (a b : ℝ) (ha : 0 < a) (hb : b ≤ 1/16)
    (H : ℕ) (hH : 4 ≤ H) (hOrder : 2 ≤ a*(H : ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) → ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      ∀ R : Finset ι, ∀ τ : ι → ℝ, ∀ T : ℝ, 0 < T → T ≤ (N : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, T₀ ≤ |τ r|) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, ∃ j ∈ NarrowPrimeBands.indices H (FixedPowerPrimeBand.primes a b N),
        1/(Real.log (N : ℝ))^100 ≤
          ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H (FixedPowerPrimeBand.primes a b N) j)
            (fun n ↦ (f n : ℂ)) (τ r)‖) →
      (∑ r ∈ R, ‖NarrowRamareRectangle.rectangle N H (FixedPowerPrimeBand.primes a b N) Q
        (fun n ↦ (f n : ℂ)) (τ r)‖^2) ≤ ε := by
  have hK := FixedPowerPrimeSamples.constant_pos a ha
  have hC := constant_pos a H ha
  let δ := Real.sqrt (ε/constant a H)
  have hδ : 0 < δ := Real.sqrt_pos.mpr (div_pos hε hC)
  have hδsq : δ^2=ε/constant a H := Real.sq_sqrt (div_nonneg hε.le hC.le)
  have hb1 : b ≤ 1 := by linarith only [hb]
  obtain ⟨NP,hNP,hPrime⟩ := FixedPowerPrimeSamples.uniform_bound (ι := ι) a b ha hb1 H hH hOrder
  obtain ⟨R₀,hR₀,T₀,hT₀,NC,hNC,hCofactor⟩ := UniformActualNarrowCofactor.uniform_bound δ hδ
  have hLogLimit := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NL,hLog⟩ := eventually_atTop.mp (hLogLimit.eventually (eventually_ge_atTop 1))
  obtain ⟨NB,hBand⟩ := eventually_atTop.mp ((FixedPowerPrimeBand.lower_tendsto a ha).eventually (eventually_ge_atTop (R₀+1)))
  refine ⟨T₀,hT₀,max 2 (max NP (max NC (max NL NB))),by omega,?_⟩
  intro N hN Q hQ f hf R τ T hT hTN htau hAway hsep hLarge
  have hN2 : 2 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hLog1 : 1 ≤ Real.log (N : ℝ) := hLog N (by omega)
  have hLogP : 0 < Real.log (N : ℝ) := by linarith only [hLog1]
  let P := FixedPowerPrimeBand.primes a b N
  let J := NarrowPrimeBands.indices H P
  let fC : ℕ → ℂ := fun n ↦ (f n : ℂ)
  have hP : ∀ p ∈ P, p.Prime ∧ R₀ < (p : ℝ) := by
    intro p hp
    have hh := FixedPowerPrimeBand.mem_primes a b N p hp
    change p.Prime ∧ (N : ℝ)^a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ)^b at hh
    have hLower : R₀+1 ≤ (N : ℝ)^a := hBand N (by omega)
    exact ⟨hh.1,by linarith only [hh.2.1,hLower]⟩
  have hfC : ∀ p ∈ P, ‖fC p‖ ≤ 1 := by
    intro p hp
    simpa only [fC,Complex.norm_real,Real.norm_eq_abs] using hf p (hP p hp).1
  have hPrimeSamples := hPrime N (by omega) fC hfC R τ T hT hTN htau hsep hLarge
  let A : ℕ → ι → ℂ := fun j r ↦ DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet N H j)
    (NarrowRamareRectangle.coefficient P Q fC) (τ r)
  let F : ℕ → ι → ℂ := fun j r ↦ DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) fC (τ r)
  have hA : ∀ j ∈ J, ∀ r ∈ R, ‖A j r‖ ≤ δ := by
    intro j hj r hr
    have hAbs : |τ r| ≤ (N : ℝ) := (abs_le.mpr (htau r hr)).trans hTN
    exact hCofactor N (by omega) P hP Q hQ f hf H j
      (FixedPowerNarrowGeometry.upper_anchor a b H N j (by omega) (by omega) hb hj) (τ r) (hAway r hr) hAbs
  have hF : ∀ j ∈ J, (∑ r ∈ R, ‖F j r‖^2) ≤ FixedPowerPrimeSamples.constant a/(Real.log (N : ℝ))^2 :=
    fun j hj ↦ hPrimeSamples j hj
  have hProduct := FiniteProductSampleBound.bound J R A F δ (FixedPowerPrimeSamples.constant a/(Real.log (N : ℝ))^2) hA hF
  have hSwap (r : ι) : (∑ j ∈ J, A j r*F j r)=NarrowRamareRectangle.rectangle N H P Q fC (τ r) := by
    unfold NarrowRamareRectangle.rectangle
    apply sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hSwap] at hProduct
  have hPrimeUpper : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ N := by
    intro p hp
    have hh := FixedPowerPrimeBand.mem_primes a b N p hp
    have hUpper : (N : ℝ)^b ≤ N := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNR hb1
    exact ⟨hh.1,hh.2.2.trans hUpper⟩
  have hJ : (J.card : ℝ) ≤ ((H : ℝ)+1)*Real.log (N : ℝ) :=
    FixedWidthLargeFrequencyCardinality.index_card_bound H N P hPrimeUpper hLog1
  have hJ2 := pow_le_pow_left₀ (Nat.cast_nonneg J.card) hJ 2
  calc
    _ ≤ (J.card : ℝ)^2*δ^2*(FixedPowerPrimeSamples.constant a/(Real.log (N : ℝ))^2) := hProduct
    _ ≤ (((H : ℝ)+1)*Real.log (N : ℝ))^2*δ^2*(FixedPowerPrimeSamples.constant a/(Real.log (N : ℝ))^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ2 (sq_nonneg δ)) (by positivity)
    _ = constant a H*δ^2 := by unfold constant; field_simp [hLogP.ne']
    _ = ε := by rw [hδsq]; field_simp [hC.ne']
end PaperP1.FixedPowerLargeRectangle
