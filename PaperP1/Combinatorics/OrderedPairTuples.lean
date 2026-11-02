module

public import PaperP1.Combinatorics.OrderedSubsetWeights
public import Mathlib.Tactic.FinCases

/-! # Exact ordered-pair and two-element-subset sums with arbitrary weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrderedPairTuples

open Finset PaperP1.Probability

variable {ι : Type*} [DecidableEq ι]

def pairs (G : Finset ι) : Finset (ι × ι) := (G ×ˢ G).filter fun p ↦ p.1 ≠ p.2

def values {G : Finset ι} (t : OrderedTuple G 2) : ι × ι := ((t 0).val, (t 1).val)

omit [DecidableEq ι] in
theorem values_injective (G : Finset ι) : Function.Injective (values (G := G)) := by
  intro t u h
  apply Function.Embedding.ext
  intro i
  apply Subtype.ext
  fin_cases i
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

theorem values_mem {G : Finset ι} (t : OrderedTuple G 2) : values t ∈ pairs G := by
  refine mem_filter.mpr ⟨mem_product.mpr ⟨(t 0).property, (t 1).property⟩, ?_⟩
  intro h
  have hi := t.injective (Subtype.ext h)
  norm_num at hi

def tuple {G : Finset ι} (x y : ι) (hx : x ∈ G) (hy : y ∈ G) (hxy : x ≠ y) :
    OrderedTuple G 2 where
  toFun i := if i = 0 then ⟨x, hx⟩ else ⟨y, hy⟩
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j
    · rfl
    · exact False.elim (hxy (congrArg Subtype.val h))
    · exact False.elim (hxy (congrArg Subtype.val h).symm)
    · rfl

omit [DecidableEq ι] in
theorem values_tuple {G : Finset ι} (x y : ι) (hx : x ∈ G) (hy : y ∈ G) (hxy : x ≠ y) :
    values (tuple x y hx hy hxy) = (x, y) := rfl

theorem image_values (G : Finset ι) : univ.image (values (G := G)) = pairs G := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, _, rfl⟩ := mem_image.mp hp
    exact values_mem t
  · intro hp
    obtain ⟨hp, hxy⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hp
    exact mem_image.mpr ⟨tuple p.1 p.2 hx hy hxy, mem_univ _, values_tuple _ _ hx hy hxy⟩

theorem set_values {G : Finset ι} (t : OrderedTuple G 2) :
    tupleValues t = {(t 0).val, (t 1).val} := by
  ext x
  rw [mem_tupleValues]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact mem_insert.mpr (Or.inl hi.symm)
    · exact mem_insert.mpr (Or.inr (mem_singleton.mpr hi.symm))
  · intro hx
    obtain hx | hx := mem_insert.mp hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, (mem_singleton.mp hx).symm⟩

theorem sum_pairs (G : Finset ι) (f : ι × ι → ℝ) :
    (∑ p ∈ pairs G, f p) = ∑ t : OrderedTuple G 2, f (values t) := by
  rw [← image_values, sum_image (values_injective G).injOn]

theorem weighted_subsets (G : Finset ι) (w : Finset ι → ℝ) :
    (∑ p ∈ pairs G, w {p.1, p.2}) = 2 * ∑ e ∈ G.powersetCard 2, w e := by
  rw [sum_pairs]
  change (∑ t : OrderedTuple G 2, w {(t 0).val, (t 1).val}) = _
  simp_rw [← set_values]
  have hp : OrderedSubsetWeights.population G 2 (G.powersetCard 2) = univ := by
    ext t
    simp only [OrderedSubsetWeights.population, mem_filter, mem_univ,
      mem_powersetCard, tupleValues_subset t, tupleValues_card t, and_self]
  have h := OrderedSubsetWeights.weighted_sum G 2 (G.powersetCard 2) (subset_refl _) w
  rw [hp] at h
  simpa only [show ((2 : ℕ).factorial : ℝ) = 2 by norm_num] using h

end PaperP1.OrderedPairTuples
