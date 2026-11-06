module

public import PaperP1.Analysis.UniformRealEulerSmallness
public import PaperP1.Analysis.FullEulerUnit
public import PaperP1.Analysis.LocalizedFrequencyBudget

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformRealEulerBudget
open Finset Filter PaperP1
open scoped Classical

theorem uniform_bound (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ → ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ)^B →
      ∀ K : ℕ, PrimeUnitMean.frequencyBudget
        (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) K ≤
          η*(Real.log (X : ℝ))^2 := by
  let C := FullEulerBound.eulerConstant
  have hCP : 0 < C := FullEulerBound.eulerConstant_pos
  let δ : ℝ := min 1 (η/20)
  have hδP : 0 < δ := by dsimp only [δ]; exact lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδη : δ ≤ η/20 := min_le_right _ _
  have hδSquare : 5*δ^2 ≤ η/4 := by
    have hh := mul_le_mul_of_nonneg_right hδ1 hδP.le
    nlinarith only [hh,hδη]
  let R : ℝ := 16*C^2/η+1
  have hRP : 0 < R := by dsimp only [R]; positivity
  have hRLower : 16*C^2/η ≤ R := by dsimp only [R]; linarith
  have hRProduct := (div_le_iff₀ hη).mp hRLower
  have hRSmall : 4*C^2/R ≤ η/4 := by
    apply (div_le_iff₀ hRP).mpr
    nlinarith only [hRProduct]
  obtain ⟨TP,hTP,hSmall⟩ := UniformRealEulerSmallness.uniform_bound (B+1) δ (by linarith only [hB]) hδP
  have hLogLim := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨XL,hXL⟩ := eventually_atTop.mp (hLogLim.eventually (eventually_ge_atTop 1))
  refine ⟨TP+R+1,by linarith only [hTP,hRP],max 2 (max XL ⌈R+2⌉₊),by omega,?_⟩
  intro X hX f hf τ hτLower hτUpper K
  have hX2 : 2 ≤ X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hXP : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hLog : 1 ≤ Real.log (X : ℝ) := hXL X (by omega)
  have hGeom : R+2 ≤ (X : ℝ) :=
    (Nat.le_ceil (R+2)).trans (by exact_mod_cast (show ⌈R+2⌉₊ ≤ X by omega))
  have hGlobal : ∀ t : ℝ,
      ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)‖ ≤ C*Real.log (X : ℝ) :=
    fun t ↦ FullEulerBound.global_bound X hX2 f hf (t+τ)
  have hLocal : ∀ u : ℝ, |u| ≤ R+1 →
      ‖RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (u+τ)‖ ≤ δ*Real.log (X : ℝ) := by
    intro u hu
    have hReverse : |τ| ≤ |u+τ|+|u| := by
      calc
        _ = |(u+τ)-u| := by congr 1; ring
        _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u+τ) u
    have hStart : TP ≤ |u+τ| := by linarith only [hReverse,hu,hτLower]
    have hPowOne : (1 : ℝ) ≤ (X : ℝ)^B := Real.one_le_rpow hX1 hB.le
    have hCross := mul_nonneg (sub_nonneg.mpr hPowOne) (sub_nonneg.mpr hX1)
    have hEnd : |u+τ| ≤ (X : ℝ)^(B+1) := by
      rw [Real.rpow_add hXP,Real.rpow_one]
      have hh : |u+τ| ≤ |u|+|τ| := by simpa only [Real.norm_eq_abs] using norm_add_le u τ
      nlinarith only [hh,hu,hτUpper,hGeom,hCross]
    exact hSmall X hX2 hLog (FixedEulerTruncation.primes X)
      (fun p hp ↦ ⟨FixedEulerTruncation.primes_prime X p hp,(mem_Icc.mp (mem_filter.mp hp).1).2⟩)
      f (fun p hp ↦ hf p (FixedEulerTruncation.primes_prime X p hp)) (u+τ) hStart hEnd
  have hCont : Continuous (fun t ↦ RealPrimeEulerBound.product (FixedEulerTruncation.primes X) f (t+τ)) :=
    (FullEulerUnit.full_continuous X f hf).comp (continuous_id.add continuous_const)
  have hRaw := LocalizedFrequencyBudget.budget_bound _ hCont
    (C*Real.log (X : ℝ)) (δ*Real.log (X : ℝ)) R hRP hGlobal hLocal K
  calc
    _ ≤ 5*(δ*Real.log (X : ℝ))^2+4*(C*Real.log (X : ℝ))^2/R := hRaw
    _ = (5*δ^2+4*C^2/R)*(Real.log (X : ℝ))^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hδSquare,hRSmall,hη]) (sq_nonneg _)
end PaperP1.UniformRealEulerBudget
