module

public import PaperP1.Model.RawValueLaw
public import PaperP1.Arithmetic.PrivatePivotGeometry

/-! # Every injective selection of private interval values has zero raw kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RawPrivateSelectedValues

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine PaperP1.PrivateValueSystem
  PaperP1.RawValueLaw PaperP1.PrivatePivotGeometry PaperP1.OddPrimePivot

variable {ι : Type*} [Fintype ι]

theorem columnMap_injective {j B : ℕ} (f : ι ↪ Fin B)
    (h1 : ∀ i, 1 < largestOddPrime (j + (f i).val))
    (hB : ∀ i, B ≤ largestOddPrime (j + (f i).val)) :
    Function.Injective (columnMap (fun i ↦ j + (f i).val)) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro u hu
  change u = 0
  funext i
  change u i = 0
  have hz := congrArg (fun z : ℕ →₀ F₂ ↦ z (largestOddPrime (j + (f i).val)))
    (LinearMap.mem_ker.mp hu)
  change (∑ k, u k • parityVec (j + (f k).val)) (largestOddPrime (j + (f i).val)) = 0 at hz
  simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul] at hz
  rw [sum_eq_single i] at hz
  · simpa only [(pivot_spec (h1 i)).2.2, mul_one] using hz
  · intro k _ hki
    rw [pivot_off_diagonal (f i) (f k) (h1 i) (hB i) (f.injective.ne hki), mul_zero]
  · simp

theorem kernel_eq_bot {j B : ℕ} (f : ι ↪ Fin B)
    (h1 : ∀ i, 1 < largestOddPrime (j + (f i).val))
    (hB : ∀ i, B ≤ largestOddPrime (j + (f i).val)) :
    LinearMap.ker (columnMap (fun i ↦ j + (f i).val)) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (columnMap_injective f h1 hB)

theorem mass_le {M j B : ℕ} (f : ι ↪ Fin B) (hj : 0 < j)
    (hcut : ∀ i, j + (f i).val ≤ M)
    (h1 : ∀ i, 1 < largestOddPrime (j + (f i).val))
    (hB : ∀ i, B ≤ largestOddPrime (j + (f i).val)) (word : ι → F₂) :
    uniformSolutionMass (valueSystem M (fun i ↦ j + (f i).val)) word ≤
      (2 ^ Fintype.card ι : ℝ)⁻¹ := by
  have hh := RawValueLaw.mass_le (fun i ↦ j + (f i).val) (by intro i; omega) hcut word
  rw [kernel_eq_bot f h1 hB, finrank_bot, pow_zero, one_div] at hh
  exact hh

end PaperP1.RawPrivateSelectedValues
