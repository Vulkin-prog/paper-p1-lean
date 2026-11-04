module

public import PaperP1.Probability.PositivePositionalConvolution

/-! # Actual probability kernels act contractively on completed positional laws

A kernel assigns a probability law to each full configuration. Its action is
the absolutely convergent atomic mixture, including for signed input laws.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalMarkovKernel

open Finset PaperP1.PositionalFiniteLaw PaperP1.FiniteConvolutionAlgebra
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCoefficientExpansion
  PaperP1.PositionalTotalMass PaperP1.PositivePositionalConvolution

variable {ι κ : Type*}

theorem summable_atoms (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) :
    Summable (fun v ↦ coeff v ν • K v) := by
  have hh : Summable (fun v ↦ ‖coeff v ν • K v‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, fun v ↦ norm_isProbability (hK v), mul_one] using
      summable_abs_coeff ν
  exact hh.of_norm

theorem norm_mixture_le (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) :
    ‖∑' v, coeff v ν • K v‖ ≤ ‖ν‖ := by
  have hs : Summable (fun v ↦ ‖coeff v ν • K v‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, fun v ↦ norm_isProbability (hK v), mul_one] using
      summable_abs_coeff ν
  calc
    _ ≤ ∑' v, ‖coeff v ν • K v‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' v, |coeff v ν| := by
      simp only [norm_smul, Real.norm_eq_abs, fun v ↦ norm_isProbability (hK v), mul_one]
    _ ≤ ‖ν‖ := tsum_abs_coeff_le ν

def action (K : Configuration ι → Space κ) (hK : ∀ v, IsProbability (K v)) :
    Space ι →L[ℝ] Space κ :=
  LinearMap.mkContinuous
    { toFun := fun ν ↦ ∑' v, coeff v ν • K v
      map_add' := fun ν μ ↦ by
        simp only [map_add, add_smul]
        exact (summable_atoms K hK ν).tsum_add (summable_atoms K hK μ)
      map_smul' := fun r ν ↦ by
        simp only [map_smul, RingHom.id_apply, smul_eq_mul, mul_smul]
        exact (summable_atoms K hK ν).tsum_const_smul r }
    1 (fun ν ↦ by
      change ‖∑' v, coeff v ν • K v‖ ≤ 1 * ‖ν‖
      rw [one_mul]
      exact norm_mixture_le K hK ν)

theorem action_eq_tsum (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) :
    action K hK ν = ∑' v, coeff v ν • K v := rfl

theorem norm_action_le (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) : ‖action K hK ν‖ ≤ ‖ν‖ :=
  norm_mixture_le K hK ν

theorem contraction (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν μ : Space ι) :
    ‖action K hK ν - action K hK μ‖ ≤ ‖ν - μ‖ := by
  rw [← map_sub]
  exact norm_action_le K hK (ν - μ)

theorem action_atom (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (v : Configuration ι) :
    action K hK (ofFinite (atom v)) = K v := by
  classical
  rw [action_eq_tsum]
  simp only [coeff_ofFinite, atom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    ite_smul, one_smul, zero_smul]
  simp

theorem coeff_action_nonneg (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι)
    (hν : ∀ v, 0 ≤ coeff v ν) (w : Configuration κ) :
    0 ≤ coeff w (action K hK ν) := by
  have hh := (summable_atoms K hK ν).hasSum.map (coeff w) (coeff w).continuous
  rw [action_eq_tsum, ← hh.tsum_eq]
  apply tsum_nonneg
  intro v
  dsimp only [Function.comp_def]
  rw [map_smul, smul_eq_mul]
  exact mul_nonneg (hν v) ((hK v).1 w)

theorem coeff_action (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) (w : Configuration κ) :
    coeff w (action K hK ν) = ∑' v, coeff v ν * coeff w (K v) := by
  have hh := (summable_atoms K hK ν).hasSum.map (coeff w) (coeff w).continuous
  rw [action_eq_tsum, ← hh.tsum_eq]
  apply tsum_congr
  intro v
  dsimp only [Function.comp_def]
  rw [map_smul, smul_eq_mul]

theorem totalMass_action (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) :
    totalMass (action K hK ν) = totalMass ν := by
  have hh := (summable_atoms K hK ν).hasSum.map totalMass totalMass.continuous
  rw [action_eq_tsum, ← hh.tsum_eq, totalMass_eq_tsum]
  apply tsum_congr
  intro v
  dsimp only [Function.comp_def]
  rw [map_smul, smul_eq_mul, (hK v).2, mul_one]

theorem action_isProbability (K : Configuration ι → Space κ)
    (hK : ∀ v, IsProbability (K v)) (ν : Space ι) (hν : IsProbability ν) :
    IsProbability (action K hK ν) :=
  ⟨coeff_action_nonneg K hK ν hν.1, (totalMass_action K hK ν).trans hν.2⟩

end PaperP1.PositionalMarkovKernel
