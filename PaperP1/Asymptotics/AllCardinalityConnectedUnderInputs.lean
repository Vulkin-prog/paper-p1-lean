module

public import PaperP1.Asymptotics.ConnectedBoundedNullityTail
public import PaperP1.Asymptotics.FixedConnectedWeightedUnderInputs

/-! # Companion T16.1 at all actual cardinalities, with the stronger exponent min{1,2-η} -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllCardinalityConnectedUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ pc pi : Parameters s, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 64) → Hypotheses pi (ε / 256) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 262144)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
          (N : ℝ) ^ (-min 1 (2 - η) + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := ConnectedBoundedNullityTail.uniform_bound η u C (ε / 2) hη hu (by positivity)
  obtain ⟨pc, pi, pp, hw⟩ := FixedConnectedWeightedUnderInputs.uniform_bound s u C (ε / 2) hu.le (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-min 1 (2 - η) + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, pc, pi, pp, ?_⟩
  intro hgeoC hgeoI hgeoP
  have hsC : (ε / 2) / 32 = ε / 64 := by ring
  have hsI : (ε / 2) / 128 = ε / 256 := by ring
  have hsP : (ε / 2) / 131072 = ε / 262144 := by ring
  obtain ⟨NW, _hNW, hw⟩ := hw (by simpa only [hsC] using hgeoC)
    (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
  refine ⟨10 + NT + NW + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ I.card < s
  let FS := F.filter P
  let FT := F.filter fun I ↦ ¬ P I
  have hsmall : (∑ I ∈ FS, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
      (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) := by
    apply (hw N (by omega) L hband G hG FS ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by have h := min_le_left (1 : ℝ) (2 - η); linarith only [h])
    · intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, hconn, _hrank⟩ := hF I hIF
      exact ⟨hIG, hthree, by dsimp only [P] at hsize; omega, hconn⟩
  have htail : (∑ I ∈ FT, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
      (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) := by
    apply (ht N (by omega) L hband FT ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by have h := min_le_right (1 : ℝ) (2 - η); linarith only [h])
    · intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, hconn, hrank⟩ := hF I hIF
      exact ⟨hIG.trans hG, hthree, by dsimp only [P] at hsize; omega, hconn, hrank⟩
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ u ^ I.card * |infiniteCenteredCoefficient L I|)
  change (∑ I ∈ FS, u ^ I.card * |infiniteCenteredCoefficient L I|) +
    (∑ I ∈ FT, u ^ I.card * |infiniteCenteredCoefficient L I|) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) ≤ (N : ℝ) ^ (-min 1 (2 - η) + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hsmall, htail, hsplit, hfactor]

theorem companion_T16_1 (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ pc pi : Parameters s, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 64) → Hypotheses pi (ε / 256) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 262144)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤
          (N : ℝ) ^ (-min (4 / 5) (2 - η) + ε) := by
  obtain ⟨s, hs, pc, pi, pp, hp⟩ := uniform_bound η u C ε hη hu hε
  refine ⟨s, hs, pc, pi, pp, ?_⟩
  intro hgeoC hgeoI hgeoP
  obtain ⟨N₀, hN₀, h⟩ := hp hgeoC hgeoI hgeoP
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband G hG F hF
  apply (h N hN L hband G hG F hF).trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  have hm : min (4 / 5 : ℝ) (2 - η) ≤ min 1 (2 - η) := min_le_min (by norm_num) le_rfl
  linarith only [hm]

end PaperP1.AllCardinalityConnectedUnderInputs
