module

public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.NarrowCofactorSparseMean
public import PaperP1.Analysis.AmplifiedPrimeProductMean
public import PaperP1.Analysis.BoundedAmplificationFactor
public import PaperP1.Analysis.RoundedAmplificationGeometry

set_option autoImplicit false
@[expose] public noncomputable section
universe u799
namespace PaperP1.ActualNarrowAmplifiedMean
open Finset PaperP1 MeasureTheory
open scoped Classical

theorem estimates (X H j l k : ℕ) (hX : 0 < X) (hH : 4 ≤ H) (hk : k ≤ H)
    (hj : (H : ℝ) ≤ NarrowPrimeBands.anchor H j) (P D Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℂ) (hfP : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hfB : ∀ n ∈ NarrowRamareRectangle.cofactorSet X H l, ‖f n‖ ≤ 1) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖(DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t)^k*
      DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l)
        (NarrowRamareRectangle.coefficient D Q f) t‖^2) ≤
      BoundedAmplificationFactor.constant*
        (T/((⌈NarrowPrimeBands.anchor H j⌉₊^k*⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ)+1)*
        AmplifiedPrimeProductMean.budget k (NarrowPrimeBands.band H P j) ∧
    ∀ {ι : Type u799} (R : Finset ι) (τ : ι → ℝ),
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∑ r ∈ R, ‖(DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f (τ r))^k*
        DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H l)
          (NarrowRamareRectangle.coefficient D Q f) (τ r)‖^2) ≤
        18*BoundedAmplificationFactor.constant*
          ((T+1)/((⌈NarrowPrimeBands.anchor H j⌉₊^k*⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊ : ℕ) : ℝ)+1)*
          AmplifiedPrimeProductMean.budget k (NarrowPrimeBands.band H P j) := by
  let A := NarrowPrimeBands.band H P j
  let B := NarrowRamareRectangle.cofactorSet X H l
  let L := ⌈NarrowPrimeBands.anchor H j⌉₊
  let U := ⌈NarrowPrimeBands.growth H*NarrowPrimeBands.anchor H j⌉₊
  let M := ⌈(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊
  let K := ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H l⌉₊
  have hu := NarrowPrimeBands.anchor_pos H j
  have hc := NarrowPrimeBands.growth_one_le H
  have hL : 0 < L := by
    have hh := Nat.one_le_ceil_iff.mpr hu
    change 1 ≤ L at hh
    omega
  have hLU : L ≤ U := Nat.ceil_le_ceil (by nlinarith only [hu,hc])
  have hALU : A ⊆ Icc L U := by
    intro p hp
    have hh := mem_Ico.mp (NarrowBandReciprocalMass.band_interval_subset H (by omega) P
      (fun p hp ↦ (hP p hp).one_le) j hp)
    exact mem_Icc.mpr ⟨hh.1,hh.2.le⟩
  have hM : 0 < M := by
    have hh := (NarrowRamareRectangle.cofactor_endpoints X H l hX).1
    change 1 ≤ M at hh
    omega
  have hMK : M ≤ K := (NarrowRamareRectangle.cofactor_endpoints X H l hX).2.1
  have hBMK : B ⊆ Icc M K := by
    intro n hn
    change n ∈ NarrowRamareRectangle.cofactorSet X H l at hn
    rw [NarrowRamareRectangle.cofactorSet_eq_interval X H l hX] at hn
    exact mem_Icc.mpr ⟨(mem_Ico.mp hn).1,(mem_Ico.mp hn).2.le⟩
  have hprime : ∀ p ∈ A, p.Prime := fun p hp ↦ hP p (NarrowPrimeBands.band_subset H P j hp)
  have hunit : ∀ p ∈ A, ‖f p‖ ≤ 1 := fun p hp ↦ hfP p (NarrowPrimeBands.band_subset H P j hp)
  have hHReal : (4 : ℝ) ≤ H := by exact_mod_cast hH
  have hanchor2 : 2 ≤ NarrowPrimeBands.anchor H j := by linarith only [hHReal,hj]
  have hMass : (∑ p ∈ A, 1/(p : ℝ)) ≤ 1 := NarrowBandReciprocalMass.mass_le_one H hH P
    (fun p hp ↦ (hP p hp).one_le) j hanchor2
  have hb : ∀ n ∈ B, ‖NarrowRamareRectangle.coefficient D Q f n‖ ≤ 1 :=
    fun n hn ↦ NarrowCofactorSparseMean.coefficient_norm_bound D Q f n (hfB n hn)
  have hspan : ((U^k*K : ℕ) : ℝ) ≤ BoundedAmplificationFactor.span*((L^k*M : ℕ) : ℝ) :=
    RoundedAmplificationGeometry.product_span_bound X H j l k hX (by omega) hj hk
  have hLM : L^k*M ≤ U^k*K := Nat.mul_le_mul (Nat.pow_le_pow_left hLU k) hMK
  have hLMpos : 0 < L^k*M := by positivity
  have hLp : (0 : ℝ) < ((L^k*M : ℕ) : ℝ) := by exact_mod_cast hLMpos
  have hbudget := AmplifiedPrimeProductMean.budget_nonneg k A
  constructor
  · have hm := AmplifiedPrimeProductMean.continuous_mean_bound k A B hprime hMass L U M K hL hLU hM hMK hALU hBMK
      f (NarrowRamareRectangle.coefficient D Q f) hunit hb T hT
    exact hm.trans (BoundedAmplificationFactor.real_factor_bound _ _ T _ hLp (Nat.cast_nonneg _) hspan hT.le hbudget)
  · intro ι R τ htau hsep
    have hm := AmplifiedPrimeProductMean.sampled_mean_bound k A B hprime hMass L U M K hL hLU hM hMK hALU hBMK
      f (NarrowRamareRectangle.coefficient D Q f) hunit hb R τ T hT htau hsep
    have hd := RoundedAmplificationGeometry.bandwidth_bound (L^k*M) (U^k*K) hLMpos hLM hspan
    exact hm.trans (BoundedAmplificationFactor.sampled_factor_bound _ _ T _ _ hLp (Nat.cast_nonneg _) hspan hT.le hbudget hd.1 hd.2)
end PaperP1.ActualNarrowAmplifiedMean
