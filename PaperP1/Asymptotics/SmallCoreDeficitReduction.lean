module

public import PaperP1.Model.SmallCoreFamilyCover
public import PaperP1.Asymptotics.UniformIndependentDeficit
public import PaperP1.Asymptotics.SublogCardinalityCap
public import PaperP1.Asymptotics.SaturationDegrees

/-! # The exact small-core reduction uses a proved uniform independent deficit -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallCoreDeficitReduction

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.SmallCoreFamilyCover PaperP1.ConnectedWindowFamilies

theorem uniform_source (v C ε : ℝ) (hv : 0 < v) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      sourceMass G L v ≤ 2 * (N : ℝ) ^ (-1 / 2 + ε) *
        ∑ D ∈ cores G L, v ^ D.card * |infiniteCenteredCoefficient L D| := by
  obtain ⟨NE, _hNE, he⟩ := PaperP1.UniformIndependentDeficit.uniform_bound 255 v C ε hv hε
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 12 (by norm_num)
  refine ⟨10 + NE + NF, by omega, ?_⟩
  intro N hN L hband G hG
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hdef (D : Finset ℕ) (hD : D ∈ cores G L) :
      PaperP1.IndependentExtensionDeficit.deficit G D
        (span (fun x ↦ squareClassSpace x L) D) L v ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    obtain ⟨hDG, _htwo, hsmall, _hcore, _hq⟩ := (mem_cores G D L).mp hD
    have hDN := hDG.trans hG
    apply he N (by omega) L hband G hG D hDN (by omega)
    exact PaperP1.IntersectionExceptional.span_le_raw D L (by
      intro x hx
      have h := (mem_Ico.mp (hDN hx)).1
      omega)
  calc
    _ ≤ 2 * ∑ D ∈ cores G L, v ^ D.card * |infiniteCenteredCoefficient L D| *
        PaperP1.IndependentExtensionDeficit.deficit G D
          (span (fun x ↦ squareClassSpace x L) D) L v := centered_source_bound G L (by omega) v hv.le
    _ ≤ 2 * ∑ D ∈ cores G L, v ^ D.card * |infiniteCenteredCoefficient L D| *
        (N : ℝ) ^ (-1 / 2 + ε) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left (hdef D hD) (mul_nonneg (pow_nonneg hv.le _) (abs_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

theorem growing_range_reduction (K : ℕ → ℕ)
    (hK : Tendsto (fun N : ℕ ↦ (K N : ℝ) / Real.log N) atTop (nhds 0))
    (u C ε : ℝ) (hu : 0 < u) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ Connected L I ∧ 256 < I.card ∧ I.card ≤ K N ∧
        (L : ℝ) / 60 < (runCompatibleNullity L I : ℝ) ∧
        (PaperP1.ChosenRelationCore.core L I).card < 256) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
        2 * (N : ℝ) ^ (-1 / 2 + ε) *
          ∑ D ∈ cores G L, (512 * u) ^ D.card * |infiniteCenteredCoefficient L D| := by
  obtain ⟨NK, _hNK, hk⟩ := PaperP1.SublogCardinalityCap.uniform_cap K hK C (1 / 960) (by norm_num)
  obtain ⟨NS, _hNS, hs⟩ := uniform_source (512 * u) C ε (by positivity) hε
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C 12 (by norm_num)
  refine ⟨10 + NK + NS + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hB : 2 ≤ L + 1 := (hf N (by omega) L hband).2.1
  have hL : 0 < L := by omega
  have hsmallF : ∀ I ∈ F, I ⊆ G ∧ Connected L I ∧ 256 < I.card ∧
      2 ≤ (PaperP1.ChosenRelationCore.core L I).card ∧
        (PaperP1.ChosenRelationCore.core L I).card < 256 := by
    intro I hI
    obtain ⟨hIG, hconn, hlarge, hsize, hhigh, hsmall⟩ := hF I hI
    have hsizeR : (I.card : ℝ) ≤ (L : ℝ) / 960 := by
      have hIR : (I.card : ℝ) ≤ K N := by exact_mod_cast hsize
      have hKR := hk N (by omega) L hband
      linarith only [hIR, hKR]
    exact ⟨hIG, hconn, hlarge, PaperP1.SmallCoreRankRetention.size_two L hL I hsizeR hhigh, hsmall⟩
  exact (finite_bound G L hL u hu.le F hsmallF).trans (hs N (by omega) L hband G hG)

end PaperP1.SmallCoreDeficitReduction
