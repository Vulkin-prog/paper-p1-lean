module

public import PaperP1.Asymptotics.SmallTransverseMassUnderInputs
public import PaperP1.Asymptotics.ResidualPrimitiveHostCount
public import PaperP1.Asymptotics.PrimitiveTripleTupleMass

/-! # Complete unconditional companion T20.8, simultaneously for all actual covers

The exceptional set is a literal finite set of primitive original triples.
Its original affine mass follows from the internal full primitive triple bound.
The exceptional set keeps its original small-component definition. Outside it, no cover can
have many small free components; the exact six-vertex packing then applies.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SixVertexBudget

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ManyPlanarSquareProducts
  PaperP1.ThreeBlockCoordinates PaperP1.TripleCoverRank PaperP1.TripleCross
  PaperP1.OrientedPlanarMotifCount

def exceptional (N L : ℕ) (C₀ : ℝ) (k : ℕ) : Finset (Fin 3 → ℕ) :=
  SmallTransverseMassUnderInputs.exceptional N L (cutoff C₀ L) k

def Budget (N L : ℕ) (C₀ : ℝ) (k : ℕ) : Prop :=
  ∀ X : Fin 3 → ℕ, RegularDirect N L X → TripleProbabilityBound.Primitive L X →
    X ∉ exceptional N L C₀ k →
    ∀ D : Finset (Vertex L), SharedPrimeCover.CoversShared X L (cutoff C₀ L) D →
      (Module.finrank F₂ (CoordinateRestrictionRank.zeroed (relativeSpace X L) D) : ℝ) ≤
        (3 * (L + 1) - (D.card : ℝ)) / 6 +
          CoverRankPrimeBudget.constant C₀ * (L + 1) / Real.log (L + 1) + 12 * (k : ℝ)

theorem uniform_budget (C C₀ ε : ℝ) (hC₀ : 1 ≤ C₀) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        mass L (exceptional N L C₀ k) ≤ (N : ℝ) ^ (-3 / 2 + ε) ∧ Budget N L C₀ k := by
  obtain ⟨NM, _hNM, hm⟩ := PrimitiveTripleTupleMass.uniform_mass C ε hε
  let k : ℕ := 1
  obtain ⟨NW, _hNW, hw⟩ := CoverRankPrimeBudget.critical_width_at_least_four C
  refine ⟨k, by dsimp [k]; decide, 10 + NW + NM, by omega, ?_⟩
  intro N hN L hband
  have hcut := cutoff_bounds hC₀ L
  have hmass := hm N (by omega) L hband (exceptional N L C₀ k) (by
    intro X hX
    have hd := SmallTransverseMassUnderInputs.exceptional_data hX
    exact ⟨hd.1.1, fun i ↦ (hd.1.2.1 i).1, hd.2.1⟩)
  refine ⟨hmass, ?_⟩
  intro X hX hprim hnot D hshared
  have hX2 (i : Fin 3) : 2 ≤ X i := (by omega : 2 ≤ N).trans (mem_Ico.mp (hX.2.1 i).1).1
  have hD := (SharedPrimeCover.cover_iff_shared (fun i ↦ (by have hh := hX2 i; omega)) hcut.1 D).mpr hshared
  have hsmall := SmallTransverseMassUnderInputs.outside_small_count (by omega) hcut.1 X hX hprim hnot D hD
  have hbudget := ComponentSixVertexBudget.residual_real_budget hX2 hcut.1
    (fun i ↦ TwoPointSquareClasses.injective_evenMap_of_rank (X i) L (hX.2.1 i).2) hX.2.2 D hD
  have hprime : 3 * ((LocalDefectBound.primeCount (cutoff C₀ L) : ℝ) + 2) ≤
      CoverRankPrimeBudget.constant C₀ * (L + 1) / Real.log (L + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      CoverRankPrimeBudget.finite_budget (hw N (by omega) L hband) hcut.1 hcut.2
  have hsmallR : (ComponentSixVertexBudget.smallCount X L (cutoff C₀ L) D : ℝ) ≤ 24 * (k : ℝ) := by
    exact_mod_cast hsmall.le
  have hsmallHalf : (ComponentSixVertexBudget.smallCount X L (cutoff C₀ L) D : ℝ) / 2 ≤ 12 * (k : ℝ) :=
    (div_le_div_of_nonneg_right hsmallR (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  calc
    _ ≤ (3 * (L + 1) - (D.card : ℝ)) / 6 +
        (ComponentSixVertexBudget.smallCount X L (cutoff C₀ L) D : ℝ) / 2 +
        3 * ((LocalDefectBound.primeCount (cutoff C₀ L) : ℝ) + 2) := hbudget
    _ ≤ (3 * (L + 1) - (D.card : ℝ)) / 6 + 12 * (k : ℝ) +
        CoverRankPrimeBudget.constant C₀ * (L + 1) / Real.log (L + 1) :=
      add_le_add (add_le_add le_rfl hsmallHalf) hprime
    _ = (3 * (L + 1) - (D.card : ℝ)) / 6 +
        CoverRankPrimeBudget.constant C₀ * (L + 1) / Real.log (L + 1) + 12 * (k : ℝ) := by ring

theorem companion_T20_8 (C C₀ η K ε : ℝ) (hC₀ : 1 ≤ C₀) (hη : 0 < η) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        mass L (exceptional N L C₀ k) ≤ (N : ℝ) ^ (-1 + ε) ∧ Budget N L C₀ k ∧
        ((ResidualPrimitiveHostCount.hosts N L C₀ η).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) ∧
        ∀ F : Finset Plane, (F.card : ℝ) ≤ (L + 1 : ℝ) ^ K →
          (∀ p ∈ F, p.1 ≠ 0 ∧ (∀ j, (↑(p.1 j).natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) ∧
            (p.2.natAbs : ℝ) ≤ (L + 1 : ℝ) ^ K) →
          ((PlanarResidualRankHosts.hosts N L C₀ η F).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
          mass L (PlanarResidualRankHosts.hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) ∧
          primitiveMass L (PlanarResidualRankHosts.hosts N L C₀ η F) ≤ (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨k, hk, NB, _hNB, hh⟩ := uniform_budget C C₀ ε hC₀ hε
  obtain ⟨NU, _hNU, hu⟩ := ResidualPrimitiveHostCount.source_unrestricted_assertion C ε hε
  obtain ⟨NP, _hNP, hp⟩ := PlanarResidualRankHosts.source_planar_assertion C C₀ η K ε hC₀ hη hε
  refine ⟨k, hk, 10 + NU + NP + NB, by omega, ?_⟩
  intro N hN L hband
  have hbudget := hh N (by omega) L hband
  exact ⟨hbudget.1.trans (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [])), hbudget.2, hu N (by omega) L hband C₀ η,
    fun F hFcard hF ↦ hp N (by omega) L hband F hFcard hF⟩

end PaperP1.SixVertexBudget
