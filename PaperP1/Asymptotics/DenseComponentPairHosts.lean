module

public import PaperP1.Asymptotics.DenseNonalignedPairs
public import PaperP1.Model.FreeComponentRank

/-! # Dense actual large-prime components force subpower nonaligned pair hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseComponentPairHosts

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.FreeComponentRank
  PaperP1.LargePrimeGraphResolution

theorem uniform_rank (C η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
      η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount x y L →
      (η / 2) * L ≤ (pairIntersectionRank x y L : ℝ) := by
  obtain ⟨K, hK, herror⟩ := companion_T9_3
  obtain ⟨NR, hr⟩ := herror C
  obtain ⟨B₀, hb⟩ := ElementaryLogGrowth.log_ge_eventually (2 * K / η)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨3 + NR + NG, by omega, ?_⟩
  intro N hN L hband x hx y hy hdense
  have hgeom := hg N (by omega) L hband
  have hlog := (hb (L + 1) hgeom.2.1).1
  have hlogpos : 0 < Real.log ((L + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < L + 1 by omega)
  have hcoef : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ η / 2 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hh := (div_le_iff₀ hη).mp hlog
    nlinarith only [hh]
  have hsmall : K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) ≤
      (η / 2) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
  have hh := (abs_le.mp (hr N (by omega) L hband x hx y hy)).2
  push_cast at hdense hsmall hh
  linarith only [hdense, hsmall, hh, hη]

theorem uniform_hosts (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_rank C η hη
  obtain ⟨NH, _hNH, hh⟩ := DenseNonalignedPairs.uniform_kernel_hosts C (η / 2) ε (by positivity) hε
  refine ⟨3 + NR + NH, by omega, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  apply hh N (by omega) L hband F hdyadic hnon
  intro p hp
  rw [TwoTargetEmptySource.dimension]
  exact hr N (by omega) L hband p.1 (hdyadic p hp).1 p.2 (hdyadic p hp).2 (hdense p hp)

end PaperP1.DenseComponentPairHosts
