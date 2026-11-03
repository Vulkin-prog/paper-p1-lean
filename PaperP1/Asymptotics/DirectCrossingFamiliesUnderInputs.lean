module

public import PaperP1.Asymptotics.DenseDirectCrossingFamiliesUnderInputs
public import PaperP1.Asymptotics.LowCrossingJointMass

/-! # Every fixed direct minimal crossing above actual sources costs N⁻¹ up to an arbitrary subpower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DirectCrossingFamiliesUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.DensePrimitiveTripleMassUnderInputs

theorem uniform_families (r s : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ A ∈ F, A ⊆ G \ e ∧ A.card = r ∧ runRelativeNullity L A = 0 ∧
        span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
        ∀ B : Finset ℕ, B ⊂ A →
          Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B)) →
      (∑ A ∈ F, infiniteJointMoment L (e ∪ A)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨p, hp⟩ := DenseDirectCrossingFamiliesUnderInputs.uniform_families r s hr C (ε / 4) (ε / 2)
    (by positivity) (by positivity)
  obtain ⟨NL, _hNL, hl⟩ := LowCrossingJointMass.uniform_bound r s (ε / 4) C (ε / 4)
    (by positivity) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo
  refine ⟨4 + ND + NL + NF, by omega, ?_⟩
  intro N hN L hband e hecard heG G hG F hF
  let W := span (fun x ↦ squareClassSpace x L) e
  let P := fun A : Finset ℕ ↦
    (MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) A : ℝ) ≤ (ε / 4) * L
  let FL := F.filter P
  let FD := F.filter fun A ↦ ¬ P A
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlow : (∑ A ∈ FL, infiniteJointMoment L (e ∪ A)) ≤
      infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := by
    have hh := hl N (by omega) L hband e hecard heG G hG FL (by
      intro A hA
      obtain ⟨hAF, hlow⟩ := mem_filter.mp hA
      obtain ⟨hAG, hcard, _hdirect, hcross, hproper⟩ := hF A hAF
      exact ⟨hAG.trans sdiff_subset, hcard,
        disjoint_left.mpr (fun x hxE hxA ↦ (mem_sdiff.mp (hAG hxA)).2 hxE), hcross, hproper, hlow⟩)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by
        have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
        linarith only [hrR])) (infiniteJointMoment_nonneg L e))
  have hdense : (∑ A ∈ FD, infiniteJointMoment L (e ∪ A)) ≤
      infiniteJointMoment L e * (N : ℝ) ^ (-1 + ε / 2) := hd N (by omega) L hband e hecard heG G hG FD (by
    intro A hA
    obtain ⟨hAF, hnot⟩ := mem_filter.mp hA
    obtain ⟨hAG, hcard, hdirect, _hcross, hproper⟩ := hF A hAF
    exact ⟨hAG, hcard, hdirect, hproper, (lt_of_not_ge hnot).le⟩)
  have hsplit := sum_filter_add_sum_filter_not F P (fun A ↦ infiniteJointMoment L (e ∪ A))
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  have hfactorE := mul_le_mul_of_nonneg_left hfactor (infiniteJointMoment_nonneg L e)
  change (∑ A ∈ FL, infiniteJointMoment L (e ∪ A)) +
    (∑ A ∈ FD, infiniteJointMoment L (e ∪ A)) = _ at hsplit
  linarith only [hlow, hdense, hsplit, hfactorE]

end PaperP1.DirectCrossingFamiliesUnderInputs
