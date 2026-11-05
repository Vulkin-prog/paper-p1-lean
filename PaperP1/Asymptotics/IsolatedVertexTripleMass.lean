module

public import PaperP1.Asymptotics.IsolatedVertexDenseTripleMass
public import PaperP1.Asymptotics.ConnectedTripleLowCrossing

/-! # All connected triples with an isolated vertex in the pair-dependence graph have joint mass N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IsolatedVertexTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.ConnectedWindowFamilies

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
        F ⊆ connectedFamilies G L 3 →
        (∀ T ∈ F, ∃ x ∈ T, ∀ y ∈ T.erase x,
          Disjoint (squareClassSpace x L) (squareClassSpace y L)) →
        (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨ND, _hND, hd⟩ := IsolatedVertexDenseTripleMass.uniform_mass C (1 / 4) (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := ConnectedTripleLowCrossing.uniform_bound (1 / 4) C (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨4 + ND + NP + NF, by omega, ?_⟩
  intro N hN L hband G hG F hF hisolated
  let Q := fun T : Finset ℕ ↦ ∃ x ∈ T,
    (Module.finrank F₂ ↥(squareClassSpace x L ⊓
      span (fun y ↦ squareClassSpace y L) (T.erase x)) : ℝ) ≤ (1 / 4 : ℝ) * L
  let FL := F.filter Q
  let FD := F.filter fun T ↦ ¬ Q T
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlo : (∑ T ∈ FL, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε / 2) :=
    (hp N (by omega) L hband G hG FL (filter_subset _ _ |>.trans hF)
      (fun _ hT ↦ (mem_filter.mp hT).2)).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only []))
  have hhi : (∑ T ∈ FD, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    apply hd N (by omega) L hband G hG FD
    · intro T hT
      exact mem_powersetCard.mp (mem_filter.mp (hF (mem_filter.mp hT).1)).1
    · intro T hT
      obtain ⟨hTF, hnot⟩ := mem_filter.mp hT
      obtain ⟨x, hx, hiso⟩ := hisolated T hTF
      refine ⟨x, hx, hiso, ?_⟩
      exact (lt_of_not_ge (fun h ↦ hnot ⟨x, hx, h⟩)).le
  have hsplit := sum_filter_add_sum_filter_not F Q (infiniteJointMoment L)
  change (∑ T ∈ FL, infiniteJointMoment L T) + (∑ T ∈ FD, infiniteJointMoment L T) = _ at hsplit
  have hfactor : 2 * (N : ℝ) ^ (-1 + ε / 2) ≤ (N : ℝ) ^ (-1 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    ring
  linarith only [hlo, hhi, hsplit, hfactor]

end PaperP1.IsolatedVertexTripleMass
