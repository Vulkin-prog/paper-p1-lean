module

public import PaperP1.Probability.PositionalKernelMoments
public import PaperP1.Probability.PositionalCountProjection

/-! # Deterministic transformations of full fields and their actual moments -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeterministicMap

open PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalTotalMass
  PaperP1.PositivePositionalConvolution PaperP1.PositionalCountProjection

variable {ι κ : Type*}

theorem atom_isProbability (v : Configuration ι) : IsProbability (ofFinite (atom v)) := by
  classical
  constructor
  · intro w
    rw [coeff_ofFinite]
    simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> norm_num
  · rw [totalMass_ofFinite, mass_atom]

def push (f : Configuration ι → Configuration κ) : Space ι →L[ℝ] Space κ :=
  PositionalMarkovKernel.action (fun v ↦ ofFinite (atom (f v))) (fun v ↦ atom_isProbability (f v))

theorem push_atom (f : Configuration ι → Configuration κ) (v : Configuration ι) :
    push f (ofFinite (atom v)) = ofFinite (atom (f v)) :=
  PositionalMarkovKernel.action_atom _ _ v

theorem contraction (f : Configuration ι → Configuration κ) (ν μ : Space ι) :
    ‖push f ν - push f μ‖ ≤ ‖ν - μ‖ :=
  PositionalMarkovKernel.contraction _ _ ν μ

theorem push_isProbability (f : Configuration ι → Configuration κ)
    (ν : Space ι) (hν : IsProbability ν) : IsProbability (push f ν) :=
  PositionalMarkovKernel.action_isProbability _ _ ν hν

theorem hasSum_atom_test (v : Configuration ι) (g : Configuration ι → ℝ) :
    HasSum (fun w ↦ coeff w (ofFinite (atom v)) * g w) (g v) := by
  classical
  have he : (fun w ↦ coeff w (ofFinite (atom v)) * g w) =
      (fun w ↦ if v = w then g v else 0) := by
    funext w
    rw [coeff_ofFinite]
    simp only [atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with hw
    · rw [hw, one_mul]
    · rw [zero_mul]
  rw [he]
  exact hasSum_ite_eq' v (g v)

theorem test_bound (f : Configuration ι → Configuration κ) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (F : Configuration ι → ℝ) (G : Configuration κ → ℝ)
    (hG : ∀ w, 0 ≤ G w) (hs : Summable (fun v ↦ coeff v ν * F v))
    (hFG : ∀ v, G (f v) ≤ F v) :
    Summable (fun w ↦ coeff w (push f ν) * G w) ∧
      (∑' w, coeff w (push f ν) * G w) ≤ ∑' v, coeff v ν * F v :=
  PositionalKernelMoments.test_bound _ _ ν hν F G hG hs
    (fun v ↦ (hasSum_atom_test (f v) G).summable)
    (fun v ↦ (hasSum_atom_test (f v) G).tsum_eq.trans_le (hFG v))

theorem polynomial_moment_bound (f : Configuration ι → Configuration κ)
    (hf : ∀ v, totalCount (f v) ≤ totalCount v) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (r : ℕ)
    (hs : Summable (fun v ↦ coeff v ν * (1 + (totalCount v : ℝ)) ^ r)) :
    Summable (fun w ↦ coeff w (push f ν) * (1 + (totalCount w : ℝ)) ^ r) ∧
      (∑' w, coeff w (push f ν) * (1 + (totalCount w : ℝ)) ^ r) ≤
        ∑' v, coeff v ν * (1 + (totalCount v : ℝ)) ^ r := by
  apply test_bound f ν hν _ _ (fun w ↦ by positivity) hs
  intro v
  apply pow_le_pow_left₀ (by positivity)
  have hh : (totalCount (f v) : ℝ) ≤ totalCount v := by exact_mod_cast hf v
  linarith only [hh]

end PaperP1.PositionalDeterministicMap
