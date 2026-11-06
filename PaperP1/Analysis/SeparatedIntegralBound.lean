module

public import PaperP1.Analysis.FiniteFrequencyCover
public import PaperP1.Analysis.UnitIntervalSampleSelection

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SeparatedIntegralBound
open Finset MeasureTheory PaperP1
open scoped Classical

theorem bound (E : Set ℝ) (T : ℝ) (g : ℝ → ℝ) (hg : Continuous g) (hgn : ∀ t, 0 ≤ g t)
    (hE : MeasurableSet E) (hEI : E ⊆ Set.Ioc (-T) T) (B : ℝ)
    (hSample : ∀ (R : Finset ℕ) (τ : ℕ → ℝ), (∀ r ∈ R, τ r ∈ E) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) → (∑ r ∈ R, g (τ r)) ≤ B) :
    (∫ t in E, g t) ≤ 4*B := by
  let J := range (⌈2*T⌉₊+1)
  let S (i : ℕ) := E ∩ UnitIntervalSampleSelection.cell (-T) i
  let A := J.filter (fun i ↦ (S i).Nonempty)
  have hSel (i : ℕ) (hi : i ∈ A) : ∃ t ∈ S i, (∫ x in S i, g x) ≤ 2*g t :=
    UnitIntervalSampleSelection.exists_sample (-T) i (S i)
      (fun _t ht ↦ ht.2) (mem_filter.mp hi).2 g hgn
  let τ (i : ℕ) : ℝ := if hi : i ∈ A then Classical.choose (hSel i hi) else 0
  have hPoint (i : ℕ) (hi : i ∈ A) : τ i ∈ S i ∧ (∫ x in S i, g x) ≤ 2*g (τ i) := by
    dsimp only [τ]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hSel i hi)
  have hCover : E ⊆ ⋃ i ∈ A, S i := by
    intro t ht
    obtain ⟨i,hi,hCell⟩ := UnitIntervalSampleSelection.cell_cover T t (hEI ht)
    have hS : t ∈ S i := ⟨ht,hCell⟩
    have hA : i ∈ A := mem_filter.mpr ⟨hi,⟨t,hS⟩⟩
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hA,hS⟩⟩
  have hMeas (i : ℕ) : MeasurableSet (S i) := hE.inter measurableSet_Icc
  have hSubset (i : ℕ) : S i ⊆ Set.Ioc (-T) T := fun _t ht ↦ hEI ht.1
  have hCoverBound := FiniteFrequencyCover.cover_bound A S E T g hg hgn hE hEI
    (fun i _hi ↦ hMeas i) (fun i _hi ↦ hSubset i) hCover
  have hSelected : (∑ i ∈ A, ∫ x in S i, g x) ≤ 2*(∑ i ∈ A, g (τ i)) := by
    have hh := sum_le_sum (s := A) (fun i hi ↦ (hPoint i hi).2)
    simpa only [← mul_sum] using hh
  have hGroup (b : ℕ) : (∑ i ∈ A.filter (fun i ↦ i%2=b), g (τ i)) ≤ B := by
    apply hSample
    · intro i hi
      exact (hPoint i (mem_filter.mp hi).1).1.1
    · intro i hi j hj hne
      obtain ⟨hiA,hiMod⟩ := mem_filter.mp hi
      obtain ⟨hjA,hjMod⟩ := mem_filter.mp hj
      exact UnitIntervalSampleSelection.cell_separated (-T) (τ i) (τ j) i j
        (hPoint i hiA).1.2 (hPoint j hjA).1.2 (hiMod.trans hjMod.symm) hne
  let A₀ := A.filter (fun i ↦ i%2=0)
  let A₁ := A.filter (fun i ↦ i%2=1)
  have hDisjoint : Disjoint A₀ A₁ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h0 : i%2=0 := (mem_filter.mp hi).2
    have h1 : i%2=1 := (mem_filter.mp hj).2
    exact Nat.zero_ne_one (h0.symm.trans h1)
  have hUnion : A₀ ∪ A₁=A := by
    ext i
    constructor
    · intro hi
      rcases mem_union.mp hi with hi | hi
      · exact (mem_filter.mp hi).1
      · exact (mem_filter.mp hi).1
    · intro hi
      have hMod : i%2 < 2 := Nat.mod_lt i (by norm_num)
      have hCases : i%2=0 ∨ i%2=1 := by omega
      rcases hCases with h | h
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hi,h⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hi,h⟩))
  have hSplit : (∑ i ∈ A, g (τ i))=(∑ i ∈ A₀, g (τ i))+(∑ i ∈ A₁, g (τ i)) := by
    rw [← sum_union hDisjoint,hUnion]
  have h0 := hGroup 0
  have h1 := hGroup 1
  change (∑ i ∈ A₀, g (τ i)) ≤ B at h0
  change (∑ i ∈ A₁, g (τ i)) ≤ B at h1
  rw [hSplit] at hSelected
  linarith only [hCoverBound,hSelected,h0,h1]
end PaperP1.SeparatedIntegralBound
