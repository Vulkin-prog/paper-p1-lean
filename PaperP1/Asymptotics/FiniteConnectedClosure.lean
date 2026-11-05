module

public import PaperP1.Asymptotics.FiniteConnectedActivity254
public import PaperP1.Asymptotics.ConnectedTail
public import PaperP1.Asymptotics.SecondOrderBoundaryCutoff

/-! # Closing the connected and primitive sums from exactly the fixed orders 3 through 256 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteConnectedClosure

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_bounds (C β ε : ℝ) (hβ : β ≤ 4 / 3) (hε : 0 < ε) :
    FiniteConnectedActivity254.Hypothesis C β →
      ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ ActualComponentRemainder.higher G L (SecondOrderBoundaryCutoff.cutoff C N) 2,
          ActualComponentRemainder.weight L 2 I) ≤ (N : ℝ) ^ (-β + ε) ∧
        (∑ I ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 I) ≤
          (N : ℝ) ^ (-β + ε) := by
  classical
  obtain ⟨NT, _hNT, ht⟩ := ConnectedTail.uniform_tail
    (SecondOrderBoundaryCutoff.cutoff C) (SecondOrderBoundaryCutoff.sublogarithmic C) 2 C (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-β + ε / 2) (ε / 2) (by positivity)
  intro hfixed
  obtain ⟨NS, _hNS, hs⟩ := FiniteConnectedActivity254.uniform_weighted 2 C β (ε / 2) (by norm_num) (by positivity) hfixed
  obtain ⟨NP, _hNP, hp⟩ := FiniteConnectedActivity254.uniform_primitives 2 C β ε (by norm_num) hβ hε hfixed
  refine ⟨10 + NF + NT + NS + NP, by omega, ?_⟩
  intro N hN L hband G hG
  refine ⟨?_, hp N (by omega) L hband G hG⟩
  let F := ActualComponentRemainder.higher G L (SecondOrderBoundaryCutoff.cutoff C N) 2
  let Small := F.filter fun I ↦ I.card ≤ 256
  let Large := F.filter fun I ↦ ¬I.card ≤ 256
  have hdata (I : Finset ℕ) (hI : I ∈ F) : I ⊆ G ∧ 3 ≤ I.card ∧
      I.card ≤ SecondOrderBoundaryCutoff.cutoff C N ∧ Connected L I ∧ runCompatibleNullity L I ≤ 2 * L := by
    obtain ⟨hIG, hthree, hsize, hconn, hcap⟩ := mem_filter.mp hI
    exact ⟨mem_powerset.mp hIG, hthree, hsize, hconn, by exact_mod_cast hcap⟩
  have hsmall : (∑ I ∈ Small, ActualComponentRemainder.weight L 2 I) ≤ (N : ℝ) ^ (-β + ε / 2) := by
    apply hs N (by omega) L hband Small
    intro I hI
    obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
    have hd := hdata I hIF
    exact ⟨hd.1.trans hG, hd.2.1, hcard, hd.2.2.2.1, hd.2.2.2.2⟩
  have hlarge : (∑ I ∈ Large, ActualComponentRemainder.weight L 2 I) ≤ (N : ℝ) ^ (-β + ε / 2) := by
    apply (ht N (by omega) L hband G hG Large ?_).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [hβ]))
    intro I hI
    obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
    have hd := hdata I hIF
    exact ⟨hd.1, hd.2.2.2.1, by omega, hd.2.2.1, hd.2.2.2.2⟩
  have hsplit := sum_filter_add_sum_filter_not F (fun I ↦ I.card ≤ 256) (ActualComponentRemainder.weight L 2)
  have hsum : (∑ I ∈ F, ActualComponentRemainder.weight L 2 I) ≤ 2 * (N : ℝ) ^ (-β + ε / 2) := by
    linarith only [hsmall, hlarge, hsplit]
  calc
    _ ≤ 2 * (N : ℝ) ^ (-β + ε / 2) := hsum
    _ ≤ (N : ℝ) ^ ((-β + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FiniteConnectedClosure
