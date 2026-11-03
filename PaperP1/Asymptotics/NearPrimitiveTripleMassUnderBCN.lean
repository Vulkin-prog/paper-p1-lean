module

public import PaperP1.Asymptotics.NearPrimitiveTripleHostsUnderBCN
public import PaperP1.Asymptotics.PointwiseRankWeightCap
public import PaperP1.Model.TripleRankGeometry

/-! # Main Proposition 12.1 for actual dense triples with weak proper intersections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NearPrimitiveTripleMassUnderBCN

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem rank_bound (I : Finset ℕ) (L : ℕ) (hcard : I.card = 3) (θ : ℝ)
    (hweak : ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
      (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ))
    (hpos : ∀ x ∈ I, 0 < x) :
    (runRelativeNullity L I : ℝ) ≤ (1 + θ) * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp (show 1 < I.card by omega)
  have hn := TripleRankGeometry.set_nullity_le_pair I hcard x y L hx hy hxy hpos
  change runRelativeNullity L I ≤ L + FreeComponentRank.pairIntersectionRank x y L at hn
  have hr : (runRelativeNullity L I : ℝ) ≤ (L : ℝ) + FreeComponentRank.pairIntersectionRank x y L := by
    exact_mod_cast hn
  have hw : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ) := hweak x hx y hy hxy
  have hL : (L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ L
  nlinarith only [hr, hw, hL]

theorem uniform_mass (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η θ ε : ℝ) (hη : 0 < η) (hθ : 0 ≤ θ) (hθsmall : θ < η / 100) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧
        η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ) ∧
        ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
          (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) →
        PrimitiveWindowMass.mass F L ≤ (N : ℝ) ^ (-2 + θ + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := NearPrimitiveTripleHostsUnderBCN.uniform_hosts
    c κ hc hBCN C η θ (ε / 2) hη hθ hθsmall (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := PointwiseRankWeightCap.uniform_bound 3 C (1 + θ) 0 (ε / 2)
    (by positivity) (by positivity)
  refine ⟨3 + NH + NW, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcount := hh N (by omega) L hband F hF
  have hpoint (I : Finset ℕ) (hI : I ∈ F) : PrimitiveWindowMass.weight L I ≤
      (N : ℝ) ^ (-2 + θ + ε / 2) := by
    obtain ⟨hcard, hIG, _hdense, hweak⟩ := hF I hI
    have hpos (x : ℕ) (hx : x ∈ I) : 0 < x := by have hh := (mem_Ico.mp (hIG hx)).1; omega
    have hrank := rank_bound I L hcard θ hweak hpos
    have hweight := hw N (by omega) L hband I hIG hcard (by simpa only [add_zero] using hrank)
    have he : -(3 : ℝ) + (1 + θ) + ε / 2 = -2 + θ + ε / 2 := by ring
    simpa only [Nat.cast_ofNat, he] using hweight
  calc
    PrimitiveWindowMass.mass F L ≤ ∑ _I ∈ F, (N : ℝ) ^ (-2 + θ + ε / 2) := sum_le_sum hpoint
    _ = (F.card : ℝ) * (N : ℝ) ^ (-2 + θ + ε / 2) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-2 + θ + ε / 2) :=
      mul_le_mul_of_nonneg_right hcount (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem main_12_1 (c κ : ℝ) (hc : 0 < c) (hBCN : PlaneCurvePointCount.UniformBound c κ)
    (C η θ ε : ℝ) (hη : 0 < η) (hθ : 0 < θ) (hθsmall : θ < η / 100) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I.card = 3 ∧ I ⊆ dyadicBlock N ∧
        η * ((L + 1 : ℕ) : ℝ) ≤ (runRelativeNullity L I : ℝ) ∧
        ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
          (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) ≤ θ * ((L + 1 : ℕ) : ℝ)) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε ∧ PrimitiveWindowMass.mass F L ≤ (N : ℝ) ^ (-2 + θ + ε) := by
  obtain ⟨NH, _hNH, hh⟩ := NearPrimitiveTripleHostsUnderBCN.uniform_hosts c κ hc hBCN C η θ ε hη hθ.le hθsmall hε
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass c κ hc hBCN C η θ ε hη hθ.le hθsmall hε
  refine ⟨3 + NH + NM, by omega, ?_⟩
  intro N hN L hband F hF
  exact ⟨hh N (by omega) L hband F hF, hm N (by omega) L hband F hF⟩

end PaperP1.NearPrimitiveTripleMassUnderBCN
