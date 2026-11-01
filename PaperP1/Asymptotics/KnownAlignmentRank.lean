module

public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem
public import PaperP1.Model.CompatibleWindowOverlap

/-! # Article 13.7 from the actual enlarged-alignment residual, including contact -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.KnownAlignmentRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss
  PaperP1.EnlargedPairGeometry

def QuantitativeConclusion (C τ : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → 0 < b → a.Coprime b → max a b ≤ (L + 1) ^ 3 →
    x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
    (pairLoss x y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / max a b +
      (2 / 3 : ℝ) * ((L + 1 : ℕ) : ℝ) * Real.log (1 / τ) ∧
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / max a b +
      (2 / 3 : ℝ) * ((L + 1 : ℕ) : ℝ) * Real.log (1 / τ)

def HeightOneConclusion (C ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L x y : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric 1 1 x y L → x ≠ y →
    0 < infiniteJointMoment L {x, y} →
    (pairLoss x y L : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) ∧
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ)

def HalfConclusion (C ε : ℝ) (N₀ : ℕ) : Prop :=
  ∀ N ≥ N₀, ∀ L a b x y : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    0 < a → 0 < b → a.Coprime b → max a b ≤ (L + 1) ^ 3 →
    x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L → x ≠ y →
    0 < infiniteJointMoment L {x, y} →
    (pairLoss x y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 + ε * ((L + 1 : ℕ) : ℝ) ∧
    (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) / 2 + ε * ((L + 1 : ℕ) : ℝ)

theorem height_one_units {x y L : ℕ} (hx : 0 < x) (hy : 0 < y)
    (hsep : x + L ≤ y ∨ y + L ≤ x) : (units 1 1 x y L).card ≤ 1 := by
  rw [← normalized_intersection_card (by norm_num : 0 < 1) (by norm_num : 0 < 1) hx hy]
  simpa only [normalized, FiniteEvenSquareClasses.dilate, one_mul, Finset.image_id'] using
    CompatibleWindowOverlap.interval_overlap_le_one hx hy hsep

theorem quantitative_bound (C τ : ℝ) (hτpos : 0 < τ) (hτlt : τ < 1) :
    ∃ N₀ : ℕ, QuantitativeConclusion C τ N₀ := by
  let ε : ℝ := (2 / 3 : ℝ) * Real.log (1 / τ)
  have hlog : 0 < Real.log (1 / τ) := Real.log_pos ((one_lt_div hτpos).mpr hτlt)
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨Ncore, hcore⟩ := EnlargedAlignedPairTheorem.uniform_bounds C ε hε
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hb hcop hheight hx hy hgeom
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hbound := (hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hb hcop hheight hx hy hgeom).2.1
  have hle : (L : ℝ) / max a b ≤ ((L + 1 : ℕ) : ℝ) / max a b :=
    div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ L) (by positivity)
  have hfull : (pairLoss x y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / max a b +
      (2 / 3 : ℝ) * ((L + 1 : ℕ) : ℝ) * Real.log (1 / τ) := by
    dsimp [ε] at hbound
    nlinarith only [hbound, hle]
  have hinter : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact ⟨hfull, hinter.trans hfull⟩

theorem height_one_bound (C ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, HeightOneConclusion C ε N₀ := by
  obtain ⟨Ncore, hcore⟩ := EnlargedAlignedPairTheorem.uniform_bounds C ε hε
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max Ncore Ngeom, ?_⟩
  intro N hN L x y hcrit hx hy halign hxy hq
  obtain ⟨hNtwo, hBtwo, _, _, _, _⟩ := hgeom N ((le_max_right _ _).trans hN) L hcrit
  have hL : 0 < L := by omega
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hsep := CompatibleWindowOverlap.compatible_pair_separated hxy hL hq
  have hu := height_one_units hxpos hypos hsep
  have hu0 : (units 1 1 x y L).card - 1 = 0 := by omega
  have hheight : max 1 1 ≤ (L + 1) ^ 3 := by
    have h := pow_pos (show 0 < L + 1 by omega) 3
    omega
  have hbound := (hcore N ((le_max_left _ _).trans hN) L 1 1 x y hcrit (by norm_num)
    (by norm_num) (by norm_num) hheight hx hy halign).1
  rw [hu0, Nat.cast_zero, zero_add] at hbound
  have hinter : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact ⟨hbound, hinter.trans hbound⟩

theorem compatible_half_bound (C ε : ℝ) (hε : 0 < ε) : ∃ N₀ : ℕ, HalfConclusion C ε N₀ := by
  obtain ⟨Ncore, hcore⟩ := EnlargedAlignedPairTheorem.uniform_bounds C ε hε
  obtain ⟨None, hone⟩ := height_one_bound C ε hε
  refine ⟨max Ncore (max None 2), ?_⟩
  intro N hN L a b x y hcrit ha hb hcop hheight hx hy halign hxy hq
  have hNtwo : 2 ≤ N := (le_max_right None 2).trans ((le_max_right _ _).trans hN)
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hfull : (pairLoss x y L : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 + ε * ((L + 1 : ℕ) : ℝ) := by
    by_cases hmax : 2 ≤ max a b
    · have hbound := (hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hb hcop hheight hx hy halign).2.1
      have hmaxR : (2 : ℝ) ≤ max a b := by exact_mod_cast hmax
      have hfrac : (L : ℝ) / max a b ≤ ((L + 1 : ℕ) : ℝ) / 2 :=
        (div_le_div_of_nonneg_left (Nat.cast_nonneg L) (by norm_num) hmaxR).trans
          (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ L) (by norm_num))
      linarith only [hbound, hfrac]
    · have ha1 : a = 1 := by have := le_max_left a b; omega
      have hb1 : b = 1 := by have := le_max_right a b; omega
      subst a
      subst b
      have hbound := (hone N ((le_max_left None 2).trans ((le_max_right _ _).trans hN))
        L x y hcrit hx hy halign hxy hq).1
      have hpos : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) / 2 := by positivity
      linarith only [hbound, hpos]
  have hinter : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact ⟨hfull, hinter.trans hfull⟩

theorem main_13_7 :
    (∀ C τ : ℝ, 0 < τ → τ < 1 → ∃ N₀, QuantitativeConclusion C τ N₀) ∧
    (∀ C ε : ℝ, 0 < ε → ∃ N₀, HalfConclusion C ε N₀) ∧
    (∀ C ε : ℝ, 0 < ε → ∃ N₀, HeightOneConclusion C ε N₀) :=
  ⟨quantitative_bound, compatible_half_bound, height_one_bound⟩

end PaperP1.KnownAlignmentRank
