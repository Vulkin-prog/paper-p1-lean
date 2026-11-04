module

public import PaperP1.Probability.PositionalMarkovKernel
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Actual nonnegative moment bounds survive a positional probability kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalKernelMoments

open PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositivePositionalConvolution PaperP1.PositionalMarkovKernel

variable {ι κ : Type*}

theorem test_bound (K : Configuration ι → Space κ) (hK : ∀ v, IsProbability (K v))
    (ν : Space ι) (hν : ∀ v, 0 ≤ coeff v ν)
    (f : Configuration ι → ℝ) (g : Configuration κ → ℝ)
    (hg : ∀ w, 0 ≤ g w) (hs : Summable (fun v ↦ coeff v ν * f v))
    (hKs : ∀ v, Summable (fun w ↦ coeff w (K v) * g w))
    (hKb : ∀ v, (∑' w, coeff w (K v) * g w) ≤ f v) :
    Summable (fun w ↦ coeff w (action K hK ν) * g w) ∧
      (∑' w, coeff w (action K hK ν) * g w) ≤ ∑' v, coeff v ν * f v := by
  let F := fun p : Configuration ι × Configuration κ ↦
    coeff p.1 ν * (coeff p.2 (K p.1) * g p.2)
  have hF (p : Configuration ι × Configuration κ) : 0 ≤ F p :=
    mul_nonneg (hν _) (mul_nonneg ((hK _).1 _) (hg _))
  have hinner (v : Configuration ι) : Summable (fun w ↦ F (v, w)) :=
    (hKs v).mul_left (coeff v ν)
  have hbound (v : Configuration ι) : (∑' w, F (v, w)) ≤ coeff v ν * f v := by
    dsimp only [F]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hKb v) (hν v)
  have houter : Summable (fun v ↦ ∑' w, F (v, w)) :=
    Summable.of_nonneg_of_le (fun v ↦ tsum_nonneg (fun w ↦ hF (v, w))) hbound hs
  have hprod : Summable F := (summable_prod_of_nonneg hF).mpr ⟨hinner, houter⟩
  have he (w : Configuration κ) : (∑' v, F (v, w)) = coeff w (action K hK ν) * g w := by
    rw [coeff_action, ← tsum_mul_right]
    apply tsum_congr
    intro v
    dsimp only [F]
    ring
  have hout : Summable (fun w ↦ coeff w (action K hK ν) * g w) := by
    have hh := hprod.prod_symm.prod
    change Summable (fun w ↦ ∑' v, F (v, w)) at hh
    simpa only [he] using hh
  refine ⟨hout, ?_⟩
  calc
    _ = ∑' w, ∑' v, F (v, w) := by simp only [he]
    _ = ∑' v, ∑' w, F (v, w) := hprod.tsum_comm
    _ ≤ _ := houter.tsum_le_tsum hbound hs

end PaperP1.PositionalKernelMoments
