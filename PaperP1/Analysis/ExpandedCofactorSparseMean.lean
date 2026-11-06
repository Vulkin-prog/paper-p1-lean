module

public import PaperP1.Analysis.NarrowCofactorSparseMean
public import PaperP1.Analysis.ExpandedCofactorRegime
public import PaperP1.Analysis.ExpandedSparseSupportedMean

set_option autoImplicit false
@[expose] public noncomputable section
universe u821
namespace PaperP1.ExpandedCofactorSparseMean
open Finset PaperP1
open scoped Classical

theorem sparse_mean_uniform :
    ∃ X₀ : ℕ, 1 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ H j : ℕ,
      NarrowPrimeBands.anchor H j ≤ (X : ℝ)^(1/16 : ℝ) →
      ∀ {ι : Type u821} (R : Finset ι) (τ : ι → ℝ) (T : ℝ), 1 ≤ T → T ≤ (X : ℝ) →
      (R.card : ℝ) ≤ (X : ℝ)^(1/18 : ℝ) →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      ∀ P Q : Finset ℕ, ∀ f : ℕ → ℂ, (∀ n ∈ NarrowRamareRectangle.cofactorSet X H j, ‖f n‖ ≤ 1) →
      (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (NarrowRamareRectangle.cofactorSet X H j)
        (NarrowRamareRectangle.coefficient P Q f) (τ r)‖^2) ≤ 10*(1+Real.log (X : ℝ)) := by
  obtain ⟨N₀,_hN₀,hs⟩ := ExpandedSparseSupportedMean.supported_uniform.{u821}
  obtain ⟨X₀,hX₀,hreg⟩ := ExpandedCofactorRegime.cofactor_regime N₀
  refine ⟨X₀,hX₀,?_⟩
  intro X hX H j hanchor ι R τ T hT hTX hR htau hsep P Q f hf
  obtain ⟨hcut,hL1,hheight,hcard,hLX⟩ := hreg X hX H j hanchor
  have hXp : 0 < X := by omega
  let L := ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
  have hh := hs L hcut R τ T hT (hTX.trans hheight) (hR.trans hcard) htau hsep
    (NarrowRamareRectangle.cofactorSet X H j) (NarrowCofactorRegime.cofactor_subset_dyadic X H j hXp)
    (NarrowRamareRectangle.coefficient P Q f) (fun n hn ↦ NarrowCofactorSparseMean.coefficient_norm_bound P Q f n (hf n hn))
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by change 1 ≤ L at hL1; omega)
  have hLXR : (L : ℝ) ≤ X := by exact_mod_cast hLX
  have hl := Real.log_le_log hLp hLXR
  exact hh.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl (1 : ℝ)) hl) (by norm_num : (0 : ℝ) ≤ 10))
end PaperP1.ExpandedCofactorSparseMean
