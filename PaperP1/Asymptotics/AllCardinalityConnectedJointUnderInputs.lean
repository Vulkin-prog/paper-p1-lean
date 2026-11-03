module

public import PaperP1.Asymptotics.ConnectedJointBoundedNullityTail
public import PaperP1.Asymptotics.FixedConnectedJointWeightedUnderInputs

/-! # Full actual connected joint mass at all cardinalities has exponent min{1,2-η} -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllCardinalityConnectedJointUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_bound (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ p : Parameters s, Hypotheses p (ε / 16) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        (∀ I ∈ F, I ⊆ G ∧ 3 ≤ I.card ∧ Connected L I ∧
          (runCompatibleNullity L I : ℝ) ≤ η * L) →
        (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤
          (N : ℝ) ^ (-min 1 (2 - η) + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := ConnectedJointBoundedNullityTail.uniform_bound η u C (ε / 2) hη hu (by positivity)
  obtain ⟨p, hw⟩ := FixedConnectedJointWeightedUnderInputs.uniform_bound s u C (ε / 2) hu.le (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-min 1 (2 - η) + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hs, p, ?_⟩
  intro hgeo
  have hscale : (ε / 2) / 8 = ε / 16 := by ring
  obtain ⟨NW, _hNW, hw⟩ := hw (by simpa only [hscale] using hgeo)
  refine ⟨10 + NT + NW + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun I : Finset ℕ ↦ I.card < s
  let FS := F.filter P
  let FT := F.filter fun I ↦ ¬ P I
  have hsmall : (∑ I ∈ FS, u ^ I.card * infiniteJointMoment L I) ≤
      (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) := by
    apply (hw N (by omega) L hband G hG FS ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by have h := min_le_left (1 : ℝ) (2 - η); linarith only [h])
    · intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, hconn, _hrank⟩ := hF I hIF
      exact ⟨hIG, hthree, by dsimp only [P] at hsize; omega, hconn⟩
  have htail : (∑ I ∈ FT, u ^ I.card * infiniteJointMoment L I) ≤
      (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) := by
    apply (ht N (by omega) L hband FT ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le hn1 (by have h := min_le_right (1 : ℝ) (2 - η); linarith only [h])
    · intro I hI
      obtain ⟨hIF, hsize⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, hconn, hrank⟩ := hF I hIF
      exact ⟨hIG.trans hG, hthree, by dsimp only [P] at hsize; omega, hconn, hrank⟩
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ u ^ I.card * infiniteJointMoment L I)
  change (∑ I ∈ FS, u ^ I.card * infiniteJointMoment L I) +
    (∑ I ∈ FT, u ^ I.card * infiniteJointMoment L I) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-min 1 (2 - η) + ε / 2) ≤ (N : ℝ) ^ (-min 1 (2 - η) + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hsmall, htail, hsplit, hfactor]

end PaperP1.AllCardinalityConnectedJointUnderInputs
