module

public import PaperP1.Asymptotics.DenseNonalignedPairs
public import PaperP1.Asymptotics.UniformGeometricCountStatement

/-! # Dense unpinned component hosts without geometric count premises

The actual component/rank error is uniformly sublinear in the window width.
The resulting host count has the stronger subpower exponent.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseComponentHostCount

open Finset PaperP1.Model PaperP1.LargePrimeGraphResolution PaperP1.FreeComponentRank

theorem uniform_rank_comparison (C δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
        |(nontrivialComponentCount x y L : ℝ) - pairIntersectionRank x y L| ≤
          δ * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, herror⟩ := FreeComponentRank.companion_T9_3
  obtain ⟨NE, he⟩ := herror C
  obtain ⟨B₀, hlog⟩ := ElementaryLogGrowth.log_ge_eventually (K / δ)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨3 + NE + NG, by omega, ?_⟩
  intro N hN L hband x hx y hy
  have hgeom := hg N (by omega) L hband
  have hlogB : 0 < Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hlarge := (hlog (L + 1) hgeom.2.1).1
  have hcoef : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ δ := by
    apply (div_le_iff₀ hlogB).mpr
    have hh := (div_le_iff₀ hδ).mp hlarge
    nlinarith only [hh]
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) :=
      he N (by omega) L hband x hx y hy
    _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)

theorem uniform_dense_rank (C η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x ∈ dyadicBlock N, ∀ y ∈ dyadicBlock N,
        η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount x y L →
          (η / 2) * ((L + 1 : ℕ) : ℝ) ≤ (pairIntersectionRank x y L : ℝ) := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_rank_comparison C (η / 2) (by positivity)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband x hx y hy hdense
  have he := (abs_le.mp (h N hN L hband x hx y hy)).2
  linarith only [he, hdense]

theorem uniform_count_of_no_exact (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ActualOffsetNonalignment.NoExact p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_dense_rank C η hη
  obtain ⟨NC, _hNC, hc⟩ := DenseNonalignedPairs.companion_T8_3_no_exact C (η / 2) ε (by positivity) hε
  refine ⟨3 + NR + NC, by omega, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  apply hc N (by omega) L hband F hdyadic hnon
  intro p hp
  exact hr N (by omega) L hband p.1 (hdyadic p hp).1 p.2 (hdyadic p hp).2 (hdense p hp)

theorem uniform_count (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NR, _hNR, hr⟩ := uniform_dense_rank C η hη
  obtain ⟨NC, _hNC, hc⟩ := DenseNonalignedPairs.companion_T8_3 C (η / 2) ε (by positivity) hε
  refine ⟨3 + NR + NC, by omega, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  apply hc N (by omega) L hband F hdyadic hnon
  intro p hp
  exact hr N (by omega) L hband p.1 (hdyadic p hp).1 p.2 (hdyadic p hp).2 (hdense p hp)

theorem dense_graph_bound (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    UniformGeometricCountStatement.DenseGraphBound C ε η := by
  obtain ⟨N₀, hN₀, h⟩ := uniform_count C η ε hη hε
  refine ⟨1, by norm_num, N₀, ?_⟩
  intro N hN L hband F hdyadic hnon hdense
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  simpa only [one_mul] using (h N hN L hband F hdyadic hnon hdense).trans
    (Real.rpow_le_rpow_of_exponent_le hn (show ε ≤ 1 / 2 + ε by linarith))

end PaperP1.DenseComponentHostCount
