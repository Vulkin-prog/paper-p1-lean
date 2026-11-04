module

public import PaperP1.Model.GoodEdgeTouchingMass
public import PaperP1.Asymptotics.IndependentTargetMass
public import PaperP1.Model.RetainedGoodEdges
public import PaperP1.Model.RetainedReferenceTheorem
public import PaperP1.Model.LocalRigidityConsequences

/-! # The independent intensity near an inserted good pair has a half-power bound

The existing actual one-source half-count replaces a graph-degree bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GoodEdgeTouchingMassRate

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ H : ℝ, ∀ r : ℕ → ℝ,
      (∀ x, 0 ≤ r x) → (∀ x ∈ RegularStarts.regularStarts N L, r x ≤ (2 ^ L : ℝ)⁻¹) →
      ∀ e ∈ GoodEdgeCompression.goodEdges H N L,
      (∑ z ∈ PositionalInsertedPair.touchingVertices (GoodEdgeCompression.goodEdges H N L) e, r z) ≤
        (N : ℝ) ^ (-1 / 2 + ε) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NI, hi⟩ := IndependentTargetMass.uniform_mass 1 C δ hδ
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ C) (-1) δ hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 4 (-1 / 2 + δ) (3 * ε / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NI + NP + NF + NG, by omega, ?_⟩
  intro N hN L hband H r hr0 hr e he
  let G := RegularStarts.regularStarts N L
  let E := GoodEdgeCompression.goodEdges H N L
  let P := (N : ℝ) ^ (-1 / 2 + δ)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := by have hh := hg N (by omega) L hband; omega
  have heG : e ⊆ G := RetainedGoodEdges.good_pair_regular (by omega) e he
  have hecard : e.card = 2 := RetainedGoodEdges.good_pair_card H N L e he
  have hE : ∀ f ∈ E, f ⊆ G ∧ f.card = 2 ∧ 0 < runRelativeNullity L f := by
    intro f hf
    exact ⟨RetainedGoodEdges.good_pair_regular (by omega) f hf,
      RetainedGoodEdges.good_pair_card H N L f hf, RetainedGoodEdges.good_pair_positive H N L f hf⟩
  have hrp (x : ℕ) (hx : x ∈ G) : r x ≤ infiniteMarginal x L := by
    rw [RetainedReferenceTheorem.ground_marginal (by omega) hL x hx]
    exact hr x hx
  have hb := GoodEdgeTouchingMass.mass_bound G L E e hE r hr0 hrp
  have hpoint (x : ℕ) (hx : x ∈ e) : r x ≤ P := by
    calc
      _ ≤ (2 ^ L : ℝ)⁻¹ := hr x (heG hx)
      _ ≤ (2 : ℝ) ^ C / N := LocalRigidityConsequences.nominal_marginal_bound (by omega) hband
      _ = (2 : ℝ) ^ C * (N : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
      _ ≤ (N : ℝ) ^ (-1 + δ) := hp N (by omega)
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [] : (-1 : ℝ) + δ ≤ -1 / 2 + δ)
  have htarget (x : ℕ) (hx : x ∈ e) :
      (∑ y ∈ WindowTargetHosts.targets G L {x}, infiniteMarginal y L) ≤ P :=
    hi N (by omega) L G {x} hband (RegularStarts.regularStarts_subset N L)
      (singleton_subset_iff.mpr (heG hx)) (card_singleton x)
  have hsumR : (∑ x ∈ e, r x) ≤ 2 * P := by
    calc
      _ ≤ ∑ _x ∈ e, P := sum_le_sum hpoint
      _ = _ := by rw [sum_const, nsmul_eq_mul, hecard]; norm_num
  have hsumT : (∑ x ∈ e, ∑ y ∈ WindowTargetHosts.targets G L {x}, infiniteMarginal y L) ≤ 2 * P := by
    calc
      _ ≤ ∑ _x ∈ e, P := sum_le_sum htarget
      _ = _ := by rw [sum_const, nsmul_eq_mul, hecard]; norm_num
  have hfactor : 4 * P ≤ (N : ℝ) ^ (-1 / 2 + ε) := by
    convert hf N (by omega) using 1
    congr 1
    dsimp [δ]
    ring
  change (∑ z ∈ PositionalInsertedPair.touchingVertices E e, r z) ≤ _
  linarith only [hb, hsumR, hsumT, hfactor]

end PaperP1.GoodEdgeTouchingMassRate
