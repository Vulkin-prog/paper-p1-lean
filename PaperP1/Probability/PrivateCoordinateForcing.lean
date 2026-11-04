/-
Adapted from Vulkin-prog/paper-c-lean, PaperCPrel8/PrivateForcing.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob 8b3cdd4e99ef9ec7fad5413a2625c830a44c9cac.
The old FinitePMF/productPMF interfaces are replaced by P1's actual normalized
finite weights and a nested uniform average. The background law is arbitrary.
-/
module

public import PaperP1.Probability.UniformFubini

/-! # Deterministic private-coordinate forcing and the full conditional law -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateCoordinateForcing

open PaperP1.Algebra PaperP1.Probability PaperP1.UniformFubini Finset

local instance privateCoordinateForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {R Ξ : Type*}

def force (target : R → Ξ) (z : R × Ξ) : R × Ξ := (z.1, target z.1)

theorem force_preserves_nonpivots (target : R → Ξ) (z : R × Ξ) :
    (force target z).1 = z.1 := rfl

theorem force_hits (target : R → Ξ) (z : R × Ξ) :
    (force target z).2 = target (force target z).1 := rfl

theorem force_fixes_satisfied (target : R → Ξ) (z : R × Ξ) (h : z.2 = target z.1) :
    force target z = z := by
  ext <;> simp [force, h]

theorem force_idempotent (target : R → Ξ) (z : R × Ξ) :
    force target (force target z) = force target z := rfl

variable [Fintype R] [Fintype Ξ] [Nonempty Ξ]

theorem forced_expectation (μ : FiniteProbability R) (target : R → Ξ) (f : R × Ξ → ℝ) :
    finiteExpectation μ.weight (fun r ↦ average (fun c ↦ f (force target (r, c)))) =
      finiteExpectation μ.weight (fun r ↦ f (r, target r)) := by
  simp only [force, constant]

theorem restricted_expectation (μ : FiniteProbability R) (target : R → Ξ)
    (f : R × Ξ → ℝ) :
    finiteExpectation μ.weight
      (fun r ↦ average (fun c ↦ if c = target r then f (r, c) else 0)) =
      (Fintype.card Ξ : ℝ)⁻¹ * finiteExpectation μ.weight (fun r ↦ f (r, target r)) := by
  classical
  simp only [average, uniformFiniteExpectation_eq, sum_ite_eq', mem_univ, ite_true]
  rw [← finiteExpectation_const_mul]
  apply congrArg (finiteExpectation μ.weight)
  funext r
  simp [div_eq_mul_inv, mul_comm]

theorem exact_conditional_expectation (μ : FiniteProbability R) (target : R → Ξ)
    (f : R × Ξ → ℝ) :
    finiteExpectation μ.weight (fun r ↦ average (fun c ↦ f (force target (r, c)))) =
      finiteExpectation μ.weight
        (fun r ↦ average (fun c ↦ if c = target r then f (r, c) else 0)) /
        (Fintype.card Ξ : ℝ)⁻¹ := by
  rw [forced_expectation, restricted_expectation]
  have hc : (Fintype.card Ξ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem forcing_event_probability (μ : FiniteProbability R) (target : R → Ξ) :
    finiteExpectation μ.weight
      (fun r ↦ average (fun c ↦ if c = target r then (1 : ℝ) else 0)) =
        (Fintype.card Ξ : ℝ)⁻¹ := by
  rw [restricted_expectation μ target (fun _ ↦ 1), finiteExpectation_const,
    μ.total_weight, one_mul, mul_one]

end PaperP1.PrivateCoordinateForcing
