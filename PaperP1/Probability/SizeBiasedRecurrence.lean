module

public import PaperP1.Probability.HermiteRecurrence

/-! # The exact size-bias interpretation of the raw recurrence norm -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SizeBiasedRecurrence

open MeasureTheory PaperP1.AtomicProbability PaperP1.PoissonSequence PaperP1.RawRecurrence
open scoped NNReal

def sizeBiased (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (hm : 0 < firstMoment P) : ProbabilityMeasure ℕ :=
  ofMass (fun k : ℕ ↦ (k : ℝ) * realMass P k / firstMoment P)
    (fun k ↦ div_nonneg (mul_nonneg (Nat.cast_nonneg _) (realMass_nonneg P k)) hm.le)
    (by
      have hs := hP.hasSum.div_const (firstMoment P)
      change HasSum _ (firstMoment P / firstMoment P) at hs
      simpa only [div_self hm.ne'] using hs)

theorem realMass_sizeBiased (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (hm : 0 < firstMoment P) (k : ℕ) :
    realMass (sizeBiased P hP hm) k = (k : ℝ) * realMass P k / firstMoment P :=
  ofMass_real_singleton _ _ _ _

def successorLaw (P : ProbabilityMeasure ℕ) : ProbabilityMeasure ℕ := P.map Nat.succ

theorem realMass_successor (P : ProbabilityMeasure ℕ) (k : ℕ) :
    realMass (successorLaw P) k = shift (realMass P) k := by
  change ((P : Measure ℕ).map Nat.succ).real {k} = _
  rw [map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton k)]
  cases k with
  | zero =>
    have heq : Nat.succ ⁻¹' ({0} : Set ℕ) = ∅ := by ext i; simp
    rw [heq, measureReal_empty, shift_zero]
  | succ k =>
    have heq : Nat.succ ⁻¹' ({k + 1} : Set ℕ) = {k} := by ext i; simp
    rw [heq]
    rfl

def singleWeight (m θ : ℝ) (hm : 0 < m) (hθm : θ ≤ m) : ℝ≥0 :=
  ⟨1 - θ / m, sub_nonneg.mpr ((div_le_one hm).mpr hθm)⟩

def doubleWeight (m θ : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) : ℝ≥0 :=
  ⟨θ / m, div_nonneg hθ hm.le⟩

def mixtureMass (P : ProbabilityMeasure ℕ) (m θ : ℝ) (k : ℕ) : ℝ :=
  (1 - θ / m) * shift (realMass P) k + (θ / m) * shift (shift (realMass P)) k

theorem mixtureMass_nonneg (P : ProbabilityMeasure ℕ) {m θ : ℝ} (hm : 0 < m) (hθ : 0 ≤ θ) (hθm : θ ≤ m) (k : ℕ) :
    0 ≤ mixtureMass P m θ k := by
  have hshift : ∀ k, 0 ≤ shift (realMass P) k := by intro k; cases k <;> simp [realMass_nonneg]
  have hshift2 : ∀ k, 0 ≤ shift (shift (realMass P)) k := by intro k; cases k <;> simp [hshift]
  exact add_nonneg (mul_nonneg (singleWeight m θ hm hθm).property (hshift k))
    (mul_nonneg (doubleWeight m θ hm hθ).property (hshift2 k))

theorem mixtureMass_hasSum (P : ProbabilityMeasure ℕ) (m θ : ℝ) : HasSum (mixtureMass P m θ) 1 := by
  have hs := ((hasSum_shift (hasSum_realMass P)).mul_left (1 - θ / m)).add
    ((hasSum_shift (hasSum_shift (hasSum_realMass P))).mul_left (θ / m))
  convert hs using 1 <;> first | rfl | ring

def shiftMixture (P : ProbabilityMeasure ℕ) (m θ : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) (hθm : θ ≤ m) : ProbabilityMeasure ℕ :=
  ofMass (mixtureMass P m θ) (mixtureMass_nonneg P hm hθ hθm) (mixtureMass_hasSum P m θ)

theorem realMass_shiftMixture (P : ProbabilityMeasure ℕ) (m θ : ℝ) (hm : 0 < m) (hθ : 0 ≤ θ) (hθm : θ ≤ m) (k : ℕ) :
    realMass (shiftMixture P m θ hm hθ hθm) k = mixtureMass P m θ k := ofMass_real_singleton _ _ _ _

theorem shiftMixture_eq_weighted_successors (P : ProbabilityMeasure ℕ) (m θ : ℝ)
    (hm : 0 < m) (hθ : 0 ≤ θ) (hθm : θ ≤ m) :
    (shiftMixture P m θ hm hθ hθm : Measure ℕ) =
      singleWeight m θ hm hθm • (successorLaw P : Measure ℕ) +
      doubleWeight m θ hm hθ • (successorLaw (successorLaw P) : Measure ℕ) := by
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  change realMass (shiftMixture P m θ hm hθ hθm) k =
    (1 - θ / m) * realMass (successorLaw P) k + (θ / m) * realMass (successorLaw (successorLaw P)) k
  rw [realMass_shiftMixture, realMass_successor, realMass_successor]
  have heq : realMass (successorLaw P) = shift (realMass P) := funext (realMass_successor P)
  rw [heq]
  rfl

theorem residual_sizeBias_identity (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (hm : 0 < firstMoment P) {θ : ℝ} (hθ : 0 ≤ θ) (hθm : θ ≤ firstMoment P) (k : ℕ) :
    residual P (firstMoment P) θ k = firstMoment P *
      (realMass (sizeBiased P hP hm) k - realMass (shiftMixture P (firstMoment P) θ hm hθ hθm) k) := by
  rw [realMass_sizeBiased, realMass_shiftMixture]
  unfold RawRecurrence.residual mixtureMass
  field_simp
  ring

theorem size_bias_totalVariation_identity (P : ProbabilityMeasure ℕ) (hP : FiniteFirstMoment P)
    (hm : 0 < firstMoment P) {θ : ℝ} (hθ : 0 ≤ θ) (hθm : θ ≤ firstMoment P) :
    norm P (firstMoment P) θ = 2 * firstMoment P *
      totalVariation (sizeBiased P hP hm) (shiftMixture P (firstMoment P) θ hm hθ hθm) := by
  unfold RawRecurrence.norm totalVariation
  have heq : (fun k ↦ |residual P (firstMoment P) θ k|) = fun k ↦ firstMoment P *
      |realMass (sizeBiased P hP hm) k - realMass (shiftMixture P (firstMoment P) θ hm hθ hθm) k| := by
    funext k
    rw [residual_sizeBias_identity P hP hm hθ hθm, abs_mul, abs_of_pos hm]
  rw [heq, tsum_mul_left]
  unfold realMass
  ring

end PaperP1.SizeBiasedRecurrence
