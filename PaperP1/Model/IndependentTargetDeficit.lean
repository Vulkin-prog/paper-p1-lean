module

public import PaperP1.Model.CenteredDependenceSupport
public import PaperP1.Affine.RetainedNullity
public import PaperP1.Model.MissingBlockProbabilities

/-! # The literal pair activity followed by an independent dependent target -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IndependentTargetDeficit

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model.InfiniteStarts

local instance independentTargetDeficitDecidable (P : Prop) : Decidable P := Classical.propDecidable P

def dependentPair (L : ℕ) (e : Finset ℕ) : Prop :=
  0 < relativeNullityOn (fun x ↦ squareClassSpace x L) e

def targetDependent (L : ℕ) (e : Finset ℕ) (z : ℕ) : Prop :=
  squareClassSpace z L ⊓ SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e ≠ ⊥

def deficit (G : Finset ℕ) (L : ℕ) : ℝ :=
  ∑ e ∈ (G.powersetCard 2).filter (dependentPair L),
    |infiniteCenteredCoefficient L e| *
      ∑ z ∈ (G \ e).filter (targetDependent L e), infiniteMarginal z L

theorem pair_rank (L x y : ℕ) (hxy : x ≠ y) :
    relativeNullityOn (fun x ↦ squareClassSpace x L) {x, y} =
      Module.finrank 𝔽₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) :=
  RetainedNullity.nullity_pair_eq_intersection _ x y hxy

theorem target_pair (L x y z : ℕ) :
    targetDependent L {x, y} z ↔ squareClassSpace z L ⊓ (squareClassSpace x L ⊔ squareClassSpace y L) ≠ ⊥ := by
  rw [targetDependent, RetainedNullity.span_pair]

theorem nonneg (G : Finset ℕ) (L : ℕ) : 0 ≤ deficit G L := by
  apply sum_nonneg
  intro e _
  apply mul_nonneg (abs_nonneg _)
  exact sum_nonneg fun z _ ↦ PaperP1.MissingBlockProbabilities.infiniteMarginal_nonneg z L

theorem incidence_formula (G : Finset ℕ) (L : ℕ) :
    deficit G L = ∑ e ∈ G.powersetCard 2, ∑ z ∈ G \ e,
      if dependentPair L e ∧ targetDependent L e z then
        |infiniteCenteredCoefficient L e| * infiniteMarginal z L else 0 := by
  unfold deficit
  rw [sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases he : dependentPair L e
  · simp only [he, true_and, ite_eq_left]
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro z _
    split_ifs <;> simp only [mul_zero]
  · simp only [he, false_and, ite_false, sum_const_zero]

end PaperP1.IndependentTargetDeficit
