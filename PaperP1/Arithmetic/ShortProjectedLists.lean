module

public import PaperP1.Asymptotics.ShortMotifBudget
public import PaperP1.Model.ProjectedSplitTuples

/-! # Actual centre lists admitting short selections projected into the old space -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortProjectedLists

open Finset PaperP1.Arithmetic PaperP1.SplitOffsetProducts PaperP1.OldSpaceProjection
open PaperP1.ShortMotifBudget PaperP1.BoundedSubsetWeights PaperP1.BoundedIntegerMotifs

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def codes (N W : ℕ) (c : ℝ) : Finset (ι → Finset ℤ) :=
  (Fintype.piFinset fun _ : ι ↦ motifs N W c).filter fun A ↦ ∀ i, Even (A i).card ∧ 2 ≤ (A i).card

def fibre (O G : Finset ℕ) (A : ι → Finset ℤ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ G).filter fun n ↦ (∑ i, parityVec (product (A i) (n i))) ∈ oldSpace O

def lists (O G : Finset ℕ) (N W : ℕ) (c : ℝ) : Finset (ι → ℕ) :=
  (Fintype.piFinset fun _ : ι ↦ G).filter fun n ↦ ∃ A ∈ codes N W c,
    (∑ i, parityVec (product (A i) (n i))) ∈ oldSpace O

theorem codes_card_le (N W : ℕ) (c : ℝ) :
    (codes (ι := ι) N W c).card ≤ (motifs N W c).card ^ Fintype.card ι := by
  have h : (codes (ι := ι) N W c).card ≤ (Fintype.piFinset fun _ : ι ↦ motifs N W c).card :=
    card_filter_le _ _
  simpa only [Fintype.card_piFinset, prod_const, card_univ] using h

theorem code_data (N W : ℕ) (c : ℝ) (harg : 0 ≤ c * Real.log (Real.log N))
    (A : ι → Finset ℤ) (hA : A ∈ codes N W c) (i : ι) :
    Even (A i).card ∧ 2 ≤ (A i).card ∧ ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧
      ∀ a ∈ A i, a.natAbs ≤ W := by
  obtain ⟨hmem, heven⟩ := mem_filter.mp hA
  have hi := Fintype.mem_piFinset.mp hmem i
  obtain ⟨hsub, hcard⟩ := (mem_boundedSubsets _ _ _).mp hi
  have hc : ((A i).card : ℝ) ≤ ⌊c * Real.log (Real.log N)⌋₊ := by exact_mod_cast hcard
  exact ⟨(heven i).1, (heven i).2, hc.trans (Nat.floor_le harg), (subset_offsets W (A i)).mp hsub⟩

theorem code_mem_of_data (N W : ℕ) (c : ℝ) (A : ι → Finset ℤ)
    (hA : ∀ i, Even (A i).card ∧ 2 ≤ (A i).card ∧ ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧
      ∀ a ∈ A i, a.natAbs ≤ W) : A ∈ codes N W c := by
  apply mem_filter.mpr
  exact ⟨Fintype.mem_piFinset.mpr (fun i ↦ mem_motifs N W c (A i) (hA i).2.2.1 (hA i).2.2.2),
    fun i ↦ ⟨(hA i).1, (hA i).2.1⟩⟩

theorem mem_lists_iff (O G : Finset ℕ) (N W : ℕ) (c : ℝ) (harg : 0 ≤ c * Real.log (Real.log N))
    (n : ι → ℕ) : n ∈ lists O G N W c ↔ (∀ i, n i ∈ G) ∧ ∃ A : ι → Finset ℤ,
      (∀ i, Even (A i).card ∧ 2 ≤ (A i).card ∧ ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧
        ∀ a ∈ A i, a.natAbs ≤ W) ∧ (∑ i, parityVec (product (A i) (n i))) ∈ oldSpace O := by
  simp only [lists, mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hblock, A, hA, hproj⟩
    exact ⟨hblock, A, code_data N W c harg A hA, hproj⟩
  · rintro ⟨hblock, A, hA, hproj⟩
    exact ⟨hblock, A, code_mem_of_data N W c A hA, hproj⟩

theorem lists_cover (O G : Finset ℕ) (N W : ℕ) (c : ℝ) :
    ∀ n ∈ lists (ι := ι) O G N W c, ∃ A ∈ codes N W c, n ∈ fibre O G A := by
  intro n hn
  simp only [lists, mem_filter] at hn
  obtain ⟨hblock, A, hA, hproj⟩ := hn
  exact ⟨A, hA, mem_filter.mpr ⟨hblock, hproj⟩⟩

theorem even_nonempty_iff (A : Finset ℤ) :
    Even A.card ∧ A.Nonempty ↔ Even A.card ∧ 2 ≤ A.card := by
  constructor
  · rintro ⟨heven, hnon⟩
    have hpos := hnon.card_pos
    obtain ⟨k, hk⟩ := heven
    exact ⟨⟨k, hk⟩, by omega⟩
  · rintro ⟨heven, hcard⟩
    exact ⟨heven, card_pos.mp (by omega)⟩

theorem mem_lists_of_even_nonempty (O G : Finset ℕ) (N W : ℕ) (c : ℝ) (n : ι → ℕ)
    (hn : ∀ i, n i ∈ G) (A : ι → Finset ℤ)
    (hA : ∀ i, Even (A i).card ∧ (A i).Nonempty ∧
      ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧ ∀ x ∈ A i, x.natAbs ≤ W)
    (hproj : (∑ i, parityVec (product (A i) (n i))) ∈ oldSpace O) : n ∈ lists O G N W c := by
  have hdata : ∀ i, Even (A i).card ∧ 2 ≤ (A i).card ∧
      ((A i).card : ℝ) ≤ c * Real.log (Real.log N) ∧ ∀ x ∈ A i, x.natAbs ≤ W := by
    intro i
    have heven := (even_nonempty_iff (A i)).mp ⟨(hA i).1, (hA i).2.1⟩
    exact ⟨heven.1, heven.2, (hA i).2.2.1, (hA i).2.2.2⟩
  simp only [lists, mem_filter, Fintype.mem_piFinset]
  exact ⟨hn, A, code_mem_of_data N W c A hdata, hproj⟩

theorem fibre_card_eq (O G : Finset ℕ) (A : ι → Finset ℤ) :
    (fibre O G A).card = (PaperP1.ProjectedSplitTuples.tuples O A (fun _ ↦ G)).card := by
  classical
  let U := PaperP1.ProjectedSplitTuples.tuples O A (fun _ ↦ G)
  let f : (ι → G) → (ι → ℕ) := fun n i ↦ (n i).val
  have hf : Function.Injective f := by
    intro n m hnm
    funext i
    exact Subtype.ext (congrFun hnm i)
  have himage : U.image f = fibre O G A := by
    ext n
    constructor
    · intro hn
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
      exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i ↦ (m i).property), (mem_filter.mp hm).2⟩
    · intro hn
      obtain ⟨hblock, hproj⟩ := mem_filter.mp hn
      let m : ι → G := fun i ↦ ⟨n i, Fintype.mem_piFinset.mp hblock i⟩
      exact mem_image.mpr ⟨m, mem_filter.mpr ⟨mem_univ _, hproj⟩, rfl⟩
  rw [← himage, card_image_of_injOn hf.injOn]

end PaperP1.ShortProjectedLists
