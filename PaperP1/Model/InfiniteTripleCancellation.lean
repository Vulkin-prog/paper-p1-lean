module

public import PaperP1.Algebra.TripleCancellationBound
public import PaperP1.Model.MissingBlockProbabilities

/-! # The exact cancellation and absolute bound for incompatible original infinite-model triples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteTripleCancellation

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Algebra PaperP1.Model PaperP1.Model.InfiniteStarts

local instance infiniteTripleCancellationMeasurableF2 : MeasurableSpace F₂ := ⊤

theorem singleton_joint (L x : ℕ) : infiniteJointMoment L {x} = infiniteMarginal x L := by
  simp only [infiniteJointMoment, prod_singleton, infiniteMarginal]

theorem coefficient_eq_transform (L : ℕ) (I : Finset ℕ) :
    infiniteCenteredCoefficient L I = centeredCoefficient (fun x ↦ infiniteMarginal x L) (infiniteJointMoment L) I :=
  infiniteCenteredCoefficient_eq_transform (I.sup (fun x ↦ x + L)) L I
    (fun _x hx ↦ le_sup (f := fun x ↦ x + L) hx)

theorem normalized (L : ℕ) {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    infiniteCenteredCoefficient L {x, y, z} = infiniteJointMoment L {x, y, z} -
      infiniteJointMoment L {x, y} * infiniteMarginal z L - infiniteJointMoment L {x, z} * infiniteMarginal y L -
      infiniteJointMoment L {y, z} * infiniteMarginal x L + 2 * infiniteMarginal x L * infiniteMarginal y L * infiniteMarginal z L := by
  rw [coefficient_eq_transform]
  exact TripleCentering.normalized _ _ hxy hxz hyz (infiniteJointMoment_empty L)
    (singleton_joint L x) (singleton_joint L y) (singleton_joint L z)

theorem incompatible_identity (L : ℕ) {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : infiniteJointMoment L {x, y, z} = 0) :
    infiniteCenteredCoefficient L {x, y, z} = -infiniteMarginal x L * infiniteMarginal y L * infiniteMarginal z L -
      infiniteCenteredCoefficient L {x, y} * infiniteMarginal z L -
      infiniteCenteredCoefficient L {x, z} * infiniteMarginal y L -
      infiniteCenteredCoefficient L {y, z} * infiniteMarginal x L := by
  rw [coefficient_eq_transform, coefficient_eq_transform L {x, y}, coefficient_eq_transform L {x, z},
    coefficient_eq_transform L {y, z}]
  exact TripleCentering.incompatible _ _ hxy hxz hyz (infiniteJointMoment_empty L)
    (singleton_joint L x) (singleton_joint L y) (singleton_joint L z) hq

theorem incompatible_bound (L : ℕ) {x y z : ℕ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hq : infiniteJointMoment L {x, y, z} = 0) :
    |infiniteCenteredCoefficient L {x, y, z}| ≤ infiniteMarginal x L * infiniteMarginal y L * infiniteMarginal z L +
      |infiniteCenteredCoefficient L {x, y}| * infiniteMarginal z L +
      |infiniteCenteredCoefficient L {x, z}| * infiniteMarginal y L +
      |infiniteCenteredCoefficient L {y, z}| * infiniteMarginal x L := by
  rw [coefficient_eq_transform, coefficient_eq_transform L {x, y}, coefficient_eq_transform L {x, z},
    coefficient_eq_transform L {y, z}]
  exact TripleCancellationBound.incompatible _ _ hxy hxz hyz (infiniteJointMoment_empty L)
    (singleton_joint L x) (singleton_joint L y) (singleton_joint L z)
    (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg y L)
    (PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg z L) hq

theorem incompatible_set_bound (L : ℕ) (I : Finset ℕ) (hI : I.card = 3)
    (hq : infiniteJointMoment L I = 0) :
    |infiniteCenteredCoefficient L I| ≤ (∏ x ∈ I, infiniteMarginal x L) +
      ∑ z ∈ I, |infiniteCenteredCoefficient L (I.erase z)| * infiniteMarginal z L := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hI
  have hbound := incompatible_bound L hxy hxz hyz hq
  convert hbound using 1
  simp [hxy, hxz, hyz, erase_insert_of_ne hxy, erase_insert_of_ne hxz, erase_insert_of_ne hyz]
  ring

end PaperP1.InfiniteTripleCancellation
