module

public import PaperP1.Asymptotics.JointFamilyProbability

/-! # Complete main Corollary 13.8 without an external geometric argument

All actual windows, critical-band quantifiers and zero-probability cases are
retained. The height-controlled rank proof supplies the former BCN use.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleRankTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FreeComponentRank PaperP1.TripleRankGeometry PaperP1.AllPairRank

theorem uniform_triple_nullity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      I.card = 3 → 0 < infiniteJointMoment L I →
        (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤ (3 / 2 + ε) * (L : ℝ) := by
  obtain ⟨Npair, hpair⟩ := compatible_pair_bound C ε hε
  refine ⟨max Npair 2, ?_⟩
  intro N hN L hband I hI hcard hq
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (by omega : 1 < I.card)
  have hsub : ({x, y} : Finset ℕ) ⊆ I := by
    intro w hw
    obtain rfl | hw := mem_insert.mp hw
    · exact hx
    · simpa only [mem_singleton.mp hw] using hy
  have hqpair : 0 < infiniteJointMoment L {x, y} := hq.trans_le (infiniteJointMoment_antitone L hsub)
  have hpos (z : ℕ) (hz : z ∈ I) : 0 < z := by
    have h := (mem_Ico.mp (hI hz)).1
    omega
  have hfinite := set_nullity_le_pair I hcard x y L hx hy hxy hpos
  have hfiniteR : (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤
      (L : ℝ) + pairIntersectionRank x y L := by exact_mod_cast hfinite
  have hrank := hpair N (by omega) L x y hband (hI hx) (hI hy) hxy hqpair
  nlinarith only [hfiniteR, hrank]

theorem uniform_nonaligned_triple_nullity (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N →
      I.card = 3 → ∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
        (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤
          (1 + (2 / 3) * Real.log 2 + ε) * (L : ℝ) := by
  obtain ⟨Npair, hpair⟩ := nonaligned_pair_bound C ε hε
  refine ⟨max Npair 2, ?_⟩
  intro N hN L hband I hI hcard x hx y hy hxy hnon
  have hpos (z : ℕ) (hz : z ∈ I) : 0 < z := by
    have h := (mem_Ico.mp (hI hz)).1
    omega
  have hfinite := set_nullity_le_pair I hcard x y L hx hy hxy hpos
  have hfiniteR : (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤
      (L : ℝ) + pairIntersectionRank x y L := by exact_mod_cast hfinite
  have hrank := hpair N (by omega) L x y hband (hI hx) (hI hy) hnon
  nlinarith only [hfiniteR, hrank]

theorem article_13_8 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ, I ⊆ dyadicBlock N → I.card = 3 →
        (0 < infiniteJointMoment L I →
          (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤ (3 / 2 + ε) * (L : ℝ)) ∧
        (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ CompressedTargetAlignment.Aligned 1 x y L →
          (relativeNullityOn (fun w ↦ squareClassSpace w L) I : ℝ) ≤
            (1 + (2 / 3) * Real.log 2 + ε) * (L : ℝ)) ∧
        infiniteJointMoment L I ≤ (N : ℝ) ^ (-3 / 2 + ε) := by
  obtain ⟨Nt, ht⟩ := uniform_triple_nullity C ε hε
  obtain ⟨Nn, hn⟩ := uniform_nonaligned_triple_nullity C ε hε
  obtain ⟨Nq, hq⟩ := JointFamilyProbability.uniform_triple_probability C ε hε
  refine ⟨max Nt (max Nn Nq), ?_⟩
  intro N hN L hband I hI hcard
  exact ⟨ht N (by omega) L hband I hI hcard,
    hn N (by omega) L hband I hI hcard, hq N (by omega) L hband I hI hcard⟩

end PaperP1.TripleRankTheorem
