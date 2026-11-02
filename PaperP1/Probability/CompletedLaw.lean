module

public import PaperP1.Probability.FiniteLawEmbedding
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Module.Completion

/-! # The completion of finite signed laws in their actual ordinary ℓ¹ norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompletedLaw

open PaperP1.Probability UniformSpace

/-- Finite signed laws equipped below with their ordinary ℓ¹ topology. -/
abbrev Finite := SignedLaw ℝ

theorem abs_coeff_le (ν : SignedLaw ℝ) (k : ℕ) : |ν.coeff k| ≤ l1Norm ν := by
  classical
  by_cases hk : k ∈ ν.coeff.support
  · exact Finset.single_le_sum (fun i _ ↦ abs_nonneg (ν.coeff i)) hk
  · rw [Finsupp.notMem_support_iff.mp hk, abs_zero]
    exact l1Norm_nonneg ν

theorem zero_of_l1Norm_eq_zero (ν : SignedLaw ℝ) (hν : l1Norm ν = 0) : ν = 0 := by
  ext k
  have h := abs_coeff_le ν k
  rw [hν] at h
  exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))

def ringNorm : RingNorm Finite where
  toFun := l1Norm
  map_zero' := l1Norm_zero
  add_le' := l1Norm_add
  neg' := l1Norm_neg
  mul_le' := l1Norm_mul
  eq_zero_of_map_eq_zero' := zero_of_l1Norm_eq_zero

instance : NormedCommRing Finite where
  __ := ringNorm.toNormedRing
  mul_comm := mul_comm

theorem norm_finite (ν : Finite) : ‖ν‖ = l1Norm ν := rfl

theorem finite_norm_smul (c : ℝ) (ν : Finite) : ‖c • ν‖ = ‖c‖ * ‖ν‖ := by
  change l1Norm (c • (ν : SignedLaw ℝ)) = ‖c‖ * l1Norm ν
  rw [FiniteLawEmbedding.l1Norm_eq_tsum, FiniteLawEmbedding.l1Norm_eq_tsum]
  change (∑' k, |c * ν.coeff k|) = ‖c‖ * ∑' k, |ν.coeff k|
  simp only [abs_mul, tsum_mul_left, Real.norm_eq_abs]

instance : NormedAlgebra ℝ Finite where
  norm_smul_le c ν := (finite_norm_smul c ν).le

instance : NormOneClass Finite := ⟨l1Norm_one⟩

abbrev Space := Completion Finite

/-- The actual finite convolution ring embeds into its norm completion. -/
def ofFinite : SignedLaw ℝ →+* Space :=
  (Completion.coeRingHom : Finite →+* Space).comp
    { toFun := fun ν ↦ (show Finite from ν)
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

theorem norm_ofFinite (ν : SignedLaw ℝ) : ‖ofFinite ν‖ = l1Norm ν :=
  Completion.norm_coe (show Finite from ν)

instance : NormOneClass Space where
  norm_one := by
    change ‖ofFinite (1 : SignedLaw ℝ)‖ = 1
    rw [norm_ofFinite, l1Norm_one]

def finiteCoeff (k : ℕ) : Finite →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun ν ↦ ν.coeff k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun ν ↦ by
      change |ν.coeff k| ≤ 1 * l1Norm ν
      simpa only [one_mul] using abs_coeff_le ν k)

/-- Singleton coefficient evaluation, continuously extended to the completion. -/
def coeff (k : ℕ) : Space →L[ℝ] ℝ := (finiteCoeff k).fromCompletion

@[simp] theorem coeff_ofFinite (ν : SignedLaw ℝ) (k : ℕ) : coeff k (ofFinite ν) = ν.coeff k :=
  ContinuousLinearMap.fromCompletion_apply_coe (finiteCoeff k) (show Finite from ν)

theorem finite_sum_abs_coeff_le (ν : Space) (s : Finset ℕ) :
    ∑ k ∈ s, |coeff k ν| ≤ ‖ν‖ := by
  induction ν using Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) continuous_norm
  | ih ν =>
    change (∑ k ∈ s, |coeff k (ofFinite ν)|) ≤ ‖ofFinite ν‖
    simp only [coeff_ofFinite, norm_ofFinite]
    rw [FiniteLawEmbedding.l1Norm_eq_tsum]
    exact Summable.sum_le_tsum s (fun k _ ↦ abs_nonneg _)
      (FiniteLawEmbedding.summable_coeff ν).abs

theorem summable_abs_coeff (ν : Space) : Summable (fun k ↦ |coeff k ν|) :=
  summable_of_sum_le (fun _ ↦ abs_nonneg _) (finite_sum_abs_coeff_le ν)

theorem tsum_abs_coeff_le (ν : Space) : (∑' k, |coeff k ν|) ≤ ‖ν‖ :=
  Real.tsum_le_of_sum_le (fun _ ↦ abs_nonneg _) (finite_sum_abs_coeff_le ν)

theorem summable_coeff (ν : Space) : Summable (fun k ↦ coeff k ν) :=
  (summable_abs_coeff ν).of_abs

/-- Every completion element has a genuine integrable atomic signed measure. -/
def toSignedMeasure (ν : Space) : MeasureTheory.SignedMeasure ℕ :=
  AtomicSignedLaw.ofSequence (fun k ↦ coeff k ν)

theorem toSignedMeasure_singleton (ν : Space) (k : ℕ) :
    toSignedMeasure ν {k} = coeff k ν :=
  AtomicSignedLaw.ofSequence_singleton (summable_coeff ν) k

end PaperP1.CompletedLaw
