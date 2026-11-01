module

public import PaperP1.Model.JointMonotonicity
public import PaperP1.Model.RegularStarts
public import PaperP1.Affine.PairNullity

/-! # A direct regular pair bounds the actual probability of any third start -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleProbabilityBound

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts

def tupleSet (X : Fin 3 → ℕ) : Finset ℕ := univ.image X

def Primitive (L : ℕ) (X : Fin 3 → ℕ) : Prop :=
  0 < relativeNullityOn (fun x ↦ squareClassSpace x L) (tupleSet X) ∧
    ∀ A : Finset ℕ, A ⊂ tupleSet X → relativeNullityOn (fun x ↦ squareClassSpace x L) A = 0

def PairGood (L : ℕ) (X : Fin 3 → ℕ) : Prop :=
  X 0 ≠ X 1 ∧ Module.finrank F₂ (squareClassSpace (X 0) L) = L ∧
    Module.finrank F₂ (squareClassSpace (X 1) L) = L ∧
    Disjoint (squareClassSpace (X 0) L) (squareClassSpace (X 1) L)

theorem marginal_of_full_rank {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hrank : Module.finrank F₂ (squareClassSpace x L) = L) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ := by
  apply PaperP1.RegularStarts.marginal_on_regular (N := x) hx hL
  exact PaperP1.RegularStarts.mem_regularStarts.mpr ⟨mem_Ico.mpr ⟨le_rfl, by omega⟩, hrank⟩

theorem pair_joint_le {x y L : ℕ} (hxy : x ≠ y) (hx : 0 < x) (hy : 0 < y) (hL : 0 < L)
    (hrankx : Module.finrank F₂ (squareClassSpace x L) = L)
    (hranky : Module.finrank F₂ (squareClassSpace y L) = L)
    (hdisj : Disjoint (squareClassSpace x L) (squareClassSpace y L)) :
    infiniteJointMoment L {x, y} ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  classical
  by_cases hq : 0 < infiniteJointMoment L {x, y}
  · have hcut (z : ℕ) (hz : z ∈ ({x, y} : Finset ℕ)) : z + L ≤ x + y + L := by
      obtain rfl | hz := mem_insert.mp hz
      · omega
      · have heq := mem_singleton.mp hz
        omega
    rw [infiniteJointMoment_exact_of_pos (x + y + L) L {x, y} hL hcut hq,
      relativeNullityOn_pair_eq_zero (fun z ↦ squareClassSpace z L) x y hxy hdisj,
      pow_zero, mul_one, prod_pair hxy, marginal_of_full_rank hx hL hrankx,
      marginal_of_full_rank hy hL hranky, pow_two]
  · exact (le_of_not_gt hq).trans (sq_nonneg _)

theorem pair_subset_tupleSet (X : Fin 3 → ℕ) : ({X 0, X 1} : Finset ℕ) ⊆ tupleSet X := by
  intro x hx
  obtain rfl | hx := mem_insert.mp hx
  · exact mem_image.mpr ⟨0, mem_univ _, rfl⟩
  · exact mem_image.mpr ⟨1, mem_univ _, (mem_singleton.mp hx).symm⟩

theorem triple_joint_le {L : ℕ} (X : Fin 3 → ℕ) (hx : 0 < X 0) (hy : 0 < X 1)
    (hL : 0 < L) (hgood : PairGood L X) :
    infiniteJointMoment L (tupleSet X) ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 := by
  exact (infiniteJointMoment_antitone L (pair_subset_tupleSet X)).trans
    (pair_joint_le hgood.1 hx hy hL hgood.2.1 hgood.2.2.1 hgood.2.2.2)

end PaperP1.TripleProbabilityBound
