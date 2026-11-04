module

public import PaperP1.Probability.PositionalKernelMoments

/-! # A positive field kernel contracts weighted signed norms

The kernel must decrease the chosen weight in expectation. In particular,
count-decreasing deletion kernels preserve every fixed polynomial weight.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalWeightedKernel

open PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositivePositionalConvolution PaperP1.PositionalMarkovKernel

variable {ι κ : Type*}

theorem abs_coeff_action_le (K : Configuration ι → Space κ) (hK : ∀ v, IsProbability (K v))
    (ν : Space ι) (w : Configuration κ) :
    |coeff w (action K hK ν)| ≤ ∑' v, |coeff v ν| * coeff w (K v) := by
  have hh := (summable_atoms K hK ν).hasSum.map (coeff w) (coeff w).continuous
  have hs : Summable (fun v ↦ coeff v ν * coeff w (K v)) := by
    simpa only [Function.comp_def, map_smul, smul_eq_mul] using hh.summable
  rw [coeff_action]
  have hb := norm_tsum_le_tsum_norm hs.norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ((hK _).1 w)] using hb

theorem weighted_bound (K : Configuration ι → Space κ) (hK : ∀ v, IsProbability (K v))
    (ν : Space ι) (f : Configuration ι → ℝ) (g : Configuration κ → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hs : Summable (fun v ↦ |coeff v ν| * f v))
    (hKs : ∀ v, Summable (fun w ↦ coeff w (K v) * g w))
    (hKb : ∀ v, (∑' w, coeff w (K v) * g w) ≤ f v) :
    Summable (fun w ↦ |coeff w (action K hK ν)| * g w) ∧
      (∑' w, |coeff w (action K hK ν)| * g w) ≤ ∑' v, |coeff v ν| * f v := by
  let F := fun p : Configuration ι × Configuration κ ↦
    |coeff p.1 ν| * (coeff p.2 (K p.1) * g p.2)
  have hF (p : Configuration ι × Configuration κ) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (mul_nonneg ((hK _).1 _) (hg _))
  have hinner (v : Configuration ι) : Summable (fun w ↦ F (v, w)) :=
    (hKs v).mul_left |coeff v ν|
  have hbound (v : Configuration ι) : (∑' w, F (v, w)) ≤ |coeff v ν| * f v := by
    dsimp only [F]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hKb v) (abs_nonneg _)
  have houter : Summable (fun v ↦ ∑' w, F (v, w)) :=
    Summable.of_nonneg_of_le (fun v ↦ tsum_nonneg (fun w ↦ hF (v, w))) hbound hs
  have hprod : Summable F := (summable_prod_of_nonneg hF).mpr ⟨hinner, houter⟩
  have hout : Summable (fun w ↦ ∑' v, F (v, w)) := by
    have hh := hprod.prod_symm.prod
    change Summable (fun w ↦ ∑' v, F (v, w)) at hh
    exact hh
  have hpoint (w : Configuration κ) : |coeff w (action K hK ν)| * g w ≤ ∑' v, F (v, w) := by
    calc
      _ ≤ (∑' v, |coeff v ν| * coeff w (K v)) * g w :=
        mul_le_mul_of_nonneg_right (abs_coeff_action_le K hK ν w) (hg w)
      _ = _ := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro v
        dsimp only [F]
        ring
  have hresult := Summable.of_nonneg_of_le
    (fun w ↦ mul_nonneg (abs_nonneg _) (hg w)) hpoint hout
  refine ⟨hresult, ?_⟩
  calc
    _ ≤ ∑' w, ∑' v, F (v, w) := hresult.tsum_le_tsum hpoint hout
    _ = ∑' v, ∑' w, F (v, w) := hprod.tsum_comm
    _ ≤ _ := houter.tsum_le_tsum hbound hs

theorem weighted_difference_bound (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν μ : Space ι)
    (f : Configuration ι → ℝ) (g : Configuration κ → ℝ) (hg : ∀ w, 0 ≤ g w)
    (hs : Summable (fun v ↦ |coeff v ν - coeff v μ| * f v))
    (hKs : ∀ v, Summable (fun w ↦ coeff w (K v) * g w))
    (hKb : ∀ v, (∑' w, coeff w (K v) * g w) ≤ f v) :
    Summable (fun w ↦ |coeff w (action K hK ν) - coeff w (action K hK μ)| * g w) ∧
      (∑' w, |coeff w (action K hK ν) - coeff w (action K hK μ)| * g w) ≤
        ∑' v, |coeff v ν - coeff v μ| * f v := by
  have hs' : Summable (fun v ↦ |coeff v (ν - μ)| * f v) := by
    simpa only [map_sub] using hs
  simpa only [map_sub] using weighted_bound K hK (ν - μ) f g hg hs' hKs hKb

end PaperP1.PositionalWeightedKernel
