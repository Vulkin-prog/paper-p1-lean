module

public import PaperP1.Arithmetic.BranchShiftCollisionPrimeBudget
public import PaperP1.Arithmetic.SmallSplitBranchPointBound

/-! # One actual integer branch certificate controls every subset and the small-branch source count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitBranchPrimeCertificate

open Finset SplitRadicalFiniteFieldPointCount BranchShiftReductionCertificate
open scoped Classical

def support {ι : Type*} [Fintype ι] (I J : ι → Finset ℤ) : Finset ℤ :=
  univ.biUnion I ∪ univ.biUnion J

theorem left_subset {ι : Type*} [Fintype ι] (I J : ι → Finset ℤ) (s : Finset ι) :
    s.biUnion I ⊆ support I J := by
  intro a ha
  obtain ⟨i, _, hai⟩ := mem_biUnion.mp ha
  exact mem_union_left _ (mem_biUnion.mpr ⟨i, mem_univ _, hai⟩)

theorem right_subset {ι : Type*} [Fintype ι] (I J : ι → Finset ℤ) (s : Finset ι) :
    s.biUnion J ⊆ support I J := by
  intro a ha
  obtain ⟨i, _, hai⟩ := mem_biUnion.mp ha
  exact mem_union_right _ (mem_biUnion.mpr ⟨i, mem_univ _, hai⟩)

theorem separable_subsets {ι : Type*} [Fintype ι] (I J : ι → Finset ℤ) (s : Finset ι)
    (p : ℕ) [Fact p.Prime] (hnot : ¬ (p : ℤ) ∣ certificate (support I J)) :
    (FormalWordPolynomials.linearOver (ZMod p) (s.biUnion I)).Separable ∧
      (FormalWordPolynomials.linearOver (ZMod p) (s.biUnion J)).Separable := by
  exact ⟨separable_on_subset _ _ (left_subset I J s) p hnot,
    separable_on_subset _ _ (right_subset I J s) p hnot⟩

theorem uniform_small_branch_count {ι : Type*} [Fintype ι] (η : ℝ) (hη : 0 < η) :
    ∃ K : ℕ, ∀ I J : ι → Finset ℤ,
      (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
      (∀ s ∈ (univ : Finset ι).powerset.erase ∅,
        ((s.biUnion I).Nonempty ∧ (s.biUnion I).card ≤ 2) ∨
        ((s.biUnion J).Nonempty ∧ (s.biUnion J).card ≤ 2)) →
      ∀ (c : ι → ℤ) (p : ℕ) (hp : p.Prime), K ≤ p →
        ¬ (p : ℤ) ∣ certificate (support I J) →
        letI : Fact p.Prime := ⟨hp⟩
        ((points (fun i ↦ (c i : ZMod p)) I J).card : ℝ) ≤ (1 + η) * (p : ℝ) ^ 2 := by
  obtain ⟨K, hK⟩ := SmallSplitBranchPointBound.uniform_upper_bound (ι := ι) η hη
  refine ⟨K, ?_⟩
  intro I J hI hJ hsmall c p hp hlarge hnot
  let : Fact p.Prime := ⟨hp⟩
  have hinj := injective_reduction (support I J) p hnot
  have hodd : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact prime_ne_two (support I J) p hnot
  have hb := hK (ZMod p) (by simpa only [ZMod.card] using hlarge) hodd
    (fun i ↦ (c i : ZMod p)) I J hI hJ (by
      intro s hs
      rcases hsmall s hs with ⟨hne, hcard⟩ | ⟨hne, hcard⟩
      · exact Or.inl ⟨hne, hcard, fun a ha b hb he ↦
          hinj (left_subset I J s ha) (left_subset I J s hb) he⟩
      · exact Or.inr ⟨hne, hcard, fun a ha b hb he ↦
          hinj (right_subset I J s ha) (right_subset I J s hb) he⟩)
  simpa only [ZMod.card] using hb

end PaperP1.SplitBranchPrimeCertificate
