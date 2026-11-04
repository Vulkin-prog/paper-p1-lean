module

public import PaperP1.Arithmetic.PolylogPivotExceptions
public import PaperP1.Model.RawDependencePairs

/-! # Exact boundary populations for the forcing deletion ledger

Translating run starts in `[N,2N)` to left boundaries gives precisely
`(N-2,N-2+N]`. Thus the translated positive-interval multiple counts
apply with no unrecorded endpoint loss.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ForcingExceptionalSets

open Finset PaperP1.Arithmetic PaperP1.Model

def boundaryBlock (N : ℕ) : Finset ℕ := (dyadicBlock N).image (fun x ↦ x - 1)

theorem mem_boundaryBlock {N j : ℕ} (hN : 2 ≤ N) :
    j ∈ boundaryBlock N ↔ j + 1 ∈ dyadicBlock N := by
  constructor
  · intro hj
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
    have hxlo := (mem_Ico.mp hx).1
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ x)] using hx
  · intro hj
    exact mem_image.mpr ⟨j + 1, hj, by omega⟩

theorem boundaryBlock_eq_interval {N : ℕ} (hN : 2 ≤ N) :
    boundaryBlock N = Ioc (N - 2) (N - 2 + N) := by
  ext j
  rw [mem_boundaryBlock hN]
  simp only [dyadicBlock, mem_Ico, mem_Ioc]
  omega

theorem boundaryBlock_card_le (N : ℕ) : (boundaryBlock N).card ≤ N := by
  exact card_image_le.trans_eq (dyadicBlock_card N)

theorem boundaryBlock_card {N : ℕ} (hN : 2 ≤ N) : (boundaryBlock N).card = N := by
  rw [boundaryBlock_eq_interval hN, Nat.card_Ioc]
  omega

def badBoundaries (N B Y : ℕ) : Finset ℕ :=
  (PaperP1.PolylogPivotExceptions.badWindows N B Y).image (fun x ↦ x - 1)

theorem mem_badBoundaries {N B Y j : ℕ} (hN : 2 ≤ N) :
    j ∈ badBoundaries N B Y ↔ j ∈ boundaryBlock N ∧
      ∃ i : Fin B, PaperP1.OddPrimePivot.largestOddPrime (j + i.val) ≤ Y := by
  constructor
  · intro hj
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hj
    obtain ⟨hx, i, hi⟩ := PaperP1.PolylogPivotExceptions.mem_badWindows.mp hx
    exact ⟨mem_image.mpr ⟨x, hx, rfl⟩, i, hi⟩
  · rintro ⟨hj, i, hi⟩
    have hs := (mem_boundaryBlock hN).mp hj
    refine mem_image.mpr ⟨j + 1, ?_, by omega⟩
    exact PaperP1.PolylogPivotExceptions.mem_badWindows.mpr ⟨hs, i, by simpa using hi⟩

theorem badBoundaries_card_le (N B Y : ℕ) :
    (badBoundaries N B Y).card ≤ (PaperP1.PolylogPivotExceptions.badWindows N B Y).card :=
  card_image_le

def dependentBoundaryPairs (M N S T : ℕ) : Finset (ℕ × ℕ) :=
  (PaperP1.RawDependencePairs.rectangularBadPairs M N S T).image
    (fun p ↦ (p.1 - 1, p.2 - 1))

theorem mem_dependentBoundaryPairs {M N S T j k : ℕ} (hN : 2 ≤ N) :
    (j, k) ∈ dependentBoundaryPairs M N S T ↔
      j ∈ boundaryBlock N ∧ k ∈ boundaryBlock N ∧
      ¬Function.Surjective (PaperP1.RawWordObservation.joint M
        (fun i : Fin S ↦ j + i.val) (fun i : Fin T ↦ k + i.val)) := by
  constructor
  · intro hp
    obtain ⟨p, hp, heq⟩ := mem_image.mp hp
    obtain ⟨hp, hn⟩ := mem_filter.mp hp
    obtain ⟨hx, hy⟩ := mem_product.mp hp
    have hj : p.1 - 1 = j := congrArg Prod.fst heq
    have hk : p.2 - 1 = k := congrArg Prod.snd heq
    refine ⟨mem_image.mpr ⟨p.1, hx, hj⟩, mem_image.mpr ⟨p.2, hy, hk⟩, ?_⟩
    simpa only [hj, hk] using hn
  · rintro ⟨hj, hk, hn⟩
    refine mem_image.mpr ⟨(j + 1, k + 1), ?_, by simp⟩
    apply mem_filter.mpr
    exact ⟨mem_product.mpr ⟨(mem_boundaryBlock hN).mp hj, (mem_boundaryBlock hN).mp hk⟩,
      by simpa using hn⟩

theorem dependentBoundaryPairs_card_le (M N S T : ℕ) :
    (dependentBoundaryPairs M N S T).card ≤
      (PaperP1.RawDependencePairs.rectangularBadPairs M N S T).card := card_image_le

end PaperP1.ForcingExceptionalSets
