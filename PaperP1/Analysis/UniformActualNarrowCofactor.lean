module

public import PaperP1.Analysis.ExpandedCofactorRegime
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.UniformRealWeightedInterval

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.UniformActualNarrowCofactor
open Finset Filter PaperP1
open scoped Classical

theorem uniform_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ H j : ℕ,
      NarrowPrimeBands.anchor H j ≤ (X : ℝ)^(1/16 : ℝ) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ) →
      ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
        (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ))) τ‖ ≤ ε := by
  obtain ⟨R,hR,T₀,hT₀,N₀,hN₀,hBound⟩ := UniformRealWeightedInterval.uniform_bound 2 ε (by norm_num) hε
  obtain ⟨X₀,hX₀,hReg⟩ := ExpandedCofactorRegime.cofactor_regime N₀
  refine ⟨R,hR,T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX P hP Q hQ f hf H j hAnchor τ hLower hUpper
  have hXP : 0 < X := by omega
  obtain ⟨hCut,hOne,hHeight,_hCard,_hLX⟩ := hReg X hX H j hAnchor
  let L : ℕ := ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hOne
  change (X : ℝ) ≤ (L : ℝ)^(9/8 : ℝ) at hHeight
  have hPower : (X : ℝ) ≤ (L : ℝ)^(2 : ℝ) := hHeight.trans
    (Real.rpow_le_rpow_of_exponent_le hLR (by norm_num : (9/8 : ℝ) ≤ 2))
  have hEndpoints := NarrowRamareRectangle.cofactor_endpoints X H j hXP
  rw [NarrowRamareRectangle.cofactorSet_eq_interval X H j hXP]
  exact hBound L hCut P hP Q hQ f hf τ hLower (hUpper.trans hPower) _ hEndpoints.2.1 hEndpoints.2.2

theorem rectangle_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 2 ≤ R ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀,
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ R < (p : ℝ)) →
      ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ H : ℕ,
      (∀ j ∈ NarrowPrimeBands.indices H P, NarrowPrimeBands.anchor H j ≤ (X : ℝ)^(1/16 : ℝ)) →
      ∀ τ : ℝ, T₀ ≤ |τ| → |τ| ≤ (X : ℝ) →
      ‖NarrowRamareRectangle.rectangle X H P Q (fun n ↦ (f n : ℂ)) τ‖ ≤
        ε*(∑ j ∈ NarrowPrimeBands.indices H P,
          ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) (fun n ↦ (f n : ℂ)) τ‖) := by
  obtain ⟨R,hR,T₀,hT₀,X₀,hX₀,hBound⟩ := uniform_bound ε hε
  refine ⟨R,hR,T₀,hT₀,X₀,hX₀,?_⟩
  intro X hX P hP Q hQ f hf H hAnchor τ hLower hUpper
  unfold NarrowRamareRectangle.rectangle
  calc
    _ ≤ ∑ j ∈ NarrowPrimeBands.indices H P,
        ‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) (fun n ↦ (f n : ℂ)) τ*
          DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
            (NarrowRamareRectangle.coefficient P Q (fun n ↦ (f n : ℂ))) τ‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ NarrowPrimeBands.indices H P,
        ε*‖DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) (fun n ↦ (f n : ℂ)) τ‖ := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      have hh := mul_le_mul_of_nonneg_left (hBound X hX P hP Q hQ f hf H j (hAnchor j hj) τ hLower hUpper)
        (norm_nonneg (DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) (fun n ↦ (f n : ℂ)) τ))
      simpa only [mul_comm] using hh
    _ = _ := by rw [mul_sum]
end PaperP1.UniformActualNarrowCofactor
