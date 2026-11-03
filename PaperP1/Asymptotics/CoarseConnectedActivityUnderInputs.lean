module

public import PaperP1.Asymptotics.IncompatibleConnectedActivityUnderInputs
public import PaperP1.Asymptotics.CoarseConnectedJointMassUnderInputs
public import PaperP1.Asymptotics.FixedContactCenteredActivity

/-! # Full actual connected activity at every prescribed bounded order has rate1, including affine incompatibility -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedActivityUnderInputs

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.CoarseConnectedParameters
  PaperP1.ConnectedWindowFamilies

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pc pi : Parameters R, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 16) → Hypotheses pi (ε / 64) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 65536)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        F ⊆ connectedFamilies G L r →
        (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨pc, hc⟩ := CoarseConnectedJointMassUnderInputs.uniform_compatible_activity R C (ε / 2) (by positivity)
  obtain ⟨pi, pp, hi⟩ := IncompatibleConnectedActivityUnderInputs.uniform_range R C (ε / 2) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨pc, pi, pp, ?_⟩
  intro hgeoC hgeoI hgeoP
  have hsC : (ε / 2) / 8 = ε / 16 := by ring
  have hsI : (ε / 2) / 32 = ε / 64 := by ring
  have hsP : (ε / 2) / 32768 = ε / 65536 := by ring
  obtain ⟨NC, _hNC, hc⟩ := hc (by simpa only [hsC] using hgeoC)
  obtain ⟨NI, _hNI, hi⟩ := hi (by simpa only [hsI] using hgeoI) (by simpa only [hsP] using hgeoP)
  refine ⟨10 + NC + NI + NF, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF
  let P := fun I : Finset ℕ ↦ 0 < infiniteJointMoment L I
  let FC := F.filter P
  let FI := F.filter fun I ↦ ¬ P I
  have hC : (∑ I ∈ FC, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    hc N (by omega) L hband r hthree hcap G hG FC (filter_subset _ _ |>.trans hF)
      (fun _ hI ↦ (mem_filter.mp hI).2)
  have hI : (∑ I ∈ FI, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply (hi N (by omega) L hband r hthree hcap G hG FI
      (filter_subset _ _ |>.trans hF) ?_).trans
    · exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])
    · intro I hI
      exact le_antisymm (le_of_not_gt (mem_filter.mp hI).2) (infiniteJointMoment_nonneg L I)
  have hsplit := sum_filter_add_sum_filter_not F P (fun I ↦ |infiniteCenteredCoefficient L I|)
  change (∑ I ∈ FC, |infiniteCenteredCoefficient L I|) + (∑ I ∈ FI, |infiniteCenteredCoefficient L I|) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hC, hI, hsplit, hfactor]

theorem companion_T14_1 (r : ℕ) (hr : 3 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ pc pi : Parameters r, ∃ pp : FinitePairDeficitInputs.Parameters,
      Hypotheses pc (ε / 16) → Hypotheses pi (ε / 64) →
      FinitePairDeficitInputs.Hypotheses pp (GeneralGraphHostCount.sizeCap (ε / 65536)) →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        CompatibleActivitySplit.absolute L (connectedFamilies G L r) ≤ (N : ℝ) ^ (-4 / 5 + ε) ∧
        CompatibleActivitySplit.absolute L (ContactCenteredTruncation.families G L r) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨pc, pi, pp, hp⟩ := uniform_range r C ε hε
  obtain ⟨NT, _hNT, ht⟩ := FixedContactCenteredActivity.uniform_bound r (by omega) C ε hε
  refine ⟨pc, pi, pp, ?_⟩
  intro hgeoC hgeoI hgeoP
  obtain ⟨NC, _hNC, hc⟩ := hp hgeoC hgeoI hgeoP
  refine ⟨10 + NC + NT, by omega, ?_⟩
  intro N hN L hband G hG
  refine ⟨?_, ht N (by omega) L hband G hG⟩
  exact (hc N (by omega) L hband r hr le_rfl G hG (connectedFamilies G L r) Subset.rfl).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only []))

end PaperP1.CoarseConnectedActivityUnderInputs
