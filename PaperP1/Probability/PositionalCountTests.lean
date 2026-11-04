module

public import PaperP1.Probability.PositionalCountProjection
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Nonnegative tests depending on the total size of a full configuration -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalCountTests

open PaperP1.PositionalFiniteLaw PaperP1.PositionalCountProjection

variable {ι : Type*}

theorem summable_test (ν : CompletedPositionalLaw.Space ι)
    (hν : ∀ v, 0 ≤ CompletedPositionalLaw.coeff v ν) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hs : Summable (fun k ↦ CompletedLaw.coeff k (projection ν) * f k)) :
    Summable (fun v ↦ CompletedPositionalLaw.coeff v ν * f (totalCount v)) := by
  have hpart : ∀ v : Configuration ι, ∃! k : ℕ, v ∈ {w | totalCount w = k} := by
    intro v
    exact ⟨totalCount v, rfl, fun k hk ↦ hk.symm⟩
  apply (summable_partition (fun v ↦ mul_nonneg (hν v) (hf _)) hpart).mpr
  constructor
  · intro k
    have hh := ((CompletedPositionalLaw.summable_coeff ν).subtype
      (fun v ↦ totalCount v = k)).mul_right (f k)
    apply hh.congr
    intro v
    change CompletedPositionalLaw.coeff v.val ν * f k =
      CompletedPositionalLaw.coeff v.val ν * f (totalCount v.val)
    rw [v.property]
  · convert hs using 1
    funext k
    rw [projection_coeff]
    exact PushforwardMass.map_mul totalCount (fun v ↦ CompletedPositionalLaw.coeff v ν) f k

theorem test_eq (ν : CompletedPositionalLaw.Space ι)
    (hν : ∀ v, 0 ≤ CompletedPositionalLaw.coeff v ν) (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hs : Summable (fun k ↦ CompletedLaw.coeff k (projection ν) * f k)) :
    (∑' v, CompletedPositionalLaw.coeff v ν * f (totalCount v)) =
      ∑' k, CompletedLaw.coeff k (projection ν) * f k := by
  simp only [projection_coeff]
  exact (PushforwardMass.test_map totalCount
    (fun v ↦ CompletedPositionalLaw.coeff v ν) f (summable_test ν hν f hf hs)).symm

end PaperP1.PositionalCountTests
