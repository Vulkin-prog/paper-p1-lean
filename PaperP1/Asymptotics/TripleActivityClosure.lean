module

public import PaperP1.Asymptotics.UnconditionalTripleControlledActivity
public import PaperP1.Asymptotics.ConnectedTail
public import PaperP1.Asymptotics.SecondOrderBoundaryCutoff

/-! # Complete connected and primitive sums controlled by the current third activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleActivityClosure

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_bounds (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
        (∑ I ∈ ActualComponentRemainder.higher G L (SecondOrderBoundaryCutoff.cutoff C N) 2,
          ActualComponentRemainder.weight L 2 I) ≤
          (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) + (N : ℝ) ^ (-4 / 3 + ε) ∧
        (∑ I ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L 2 I) ≤
          (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (G.powersetCard 3) + (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  obtain ⟨NF, _hNF, hf⟩ := UnconditionalTripleControlledActivity.uniform_weighted 256 2 C (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NT, _hNT, ht⟩ := ConnectedTail.uniform_tail
    (SecondOrderBoundaryCutoff.cutoff C) (SecondOrderBoundaryCutoff.sublogarithmic C) 2 C (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := Primitive256Tail.uniform_centered 2 C (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NA, habs⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NP + NA + NF + NT, by omega, ?_⟩
  intro N hN L hband G hG
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let A3 := CompatibleActivitySplit.absolute L (G.powersetCard 3)
  let P := (N : ℝ) ^ (-4 / 3 + ε / 2)
  have hA3 : 0 ≤ A3 := sum_nonneg fun I _ ↦ abs_nonneg _
  have hcombine (a b : ℝ) (ha : a ≤ (N : ℝ) ^ (ε / 2) * A3 + P) (hb : b ≤ P) :
      a + b ≤ (N : ℝ) ^ ε * A3 + (N : ℝ) ^ (-4 / 3 + ε) := by
    have hcoeff : (N : ℝ) ^ (ε / 2) * A3 ≤ (N : ℝ) ^ ε * A3 :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hA3
    have hfactor : 2 * P ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
      convert habs N (by omega) using 1
      congr 1
      ring
    linarith only [ha, hb, hcoeff, hfactor]
  constructor
  · let F := ActualComponentRemainder.higher G L (SecondOrderBoundaryCutoff.cutoff C N) 2
    let Small := F.filter fun I ↦ I.card ≤ 256
    let Large := F.filter fun I ↦ ¬ I.card ≤ 256
    have hdata (I : Finset ℕ) (hI : I ∈ F) : I ⊆ G ∧ 3 ≤ I.card ∧
        I.card ≤ SecondOrderBoundaryCutoff.cutoff C N ∧ Connected L I ∧ runCompatibleNullity L I ≤ 2 * L := by
      obtain ⟨hIG, hthree, hsize, hconn, hcap⟩ := mem_filter.mp hI
      exact ⟨mem_powerset.mp hIG, hthree, hsize, hconn, by exact_mod_cast hcap⟩
    have hsmall : (∑ I ∈ Small, ActualComponentRemainder.weight L 2 I) ≤ (N : ℝ) ^ (ε / 2) * A3 + P := by
      apply hf N (by omega) L hband G hG Small
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      have hd := hdata I hIF
      exact ⟨hd.1, hd.2.1, hcard, hd.2.2.2.1⟩
    have hlarge : (∑ I ∈ Large, ActualComponentRemainder.weight L 2 I) ≤ P := by
      apply (ht N (by omega) L hband G hG Large ?_).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      have hd := hdata I hIF
      exact ⟨hd.1, hd.2.2.2.1, by omega, hd.2.2.1, hd.2.2.2.2⟩
    have hsplit := sum_filter_add_sum_filter_not F (fun I ↦ I.card ≤ 256) (ActualComponentRemainder.weight L 2)
    exact hsplit ▸ hcombine _ _ hsmall hlarge
  · let F := SecondOrderIndependentDeficit.primitives G L
    let Small := F.filter fun I ↦ I.card ≤ 256
    let Large := F.filter fun I ↦ ¬ I.card ≤ 256
    have hsmall : (∑ I ∈ Small, ActualComponentRemainder.weight L 2 I) ≤ (N : ℝ) ^ (ε / 2) * A3 + P := by
      apply hf N (by omega) L hband G hG Small
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      obtain ⟨hIG, hthree, hprim⟩ := mem_filter.mp hIF
      exact ⟨mem_powerset.mp hIG, hthree, hcard, PrimitiveConnectedGeometry.connected L I hprim⟩
    have hlarge : (∑ I ∈ Large, ActualComponentRemainder.weight L 2 I) ≤ P := by
      apply (hp N (by omega) L hband Large ?_).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      obtain ⟨hIG, _hthree, hprim⟩ := mem_filter.mp hIF
      exact ⟨(mem_powerset.mp hIG).trans hG, by omega, hprim⟩
    have hsplit := sum_filter_add_sum_filter_not F (fun I ↦ I.card ≤ 256) (ActualComponentRemainder.weight L 2)
    exact hsplit ▸ hcombine _ _ hsmall hlarge

end PaperP1.TripleActivityClosure
