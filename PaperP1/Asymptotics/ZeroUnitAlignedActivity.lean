module

public import PaperP1.Model.AlignedChannelFamilies
public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem
public import PaperP1.Asymptotics.WeakPairActivity

/-! # Zero-unit enlarged alignments have only N^(-1+epsilon) actual centered activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroUnitAlignedActivity

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.AlignedChannelFamilies
  PaperP1.DependentFamilySeeds

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      CompatibleActivitySplit.absolute L (zeroFamilies N L) ≤ (N : ℝ) ^ (-1 + ε) := by
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NR, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C (η / 2) (by positivity)
  obtain ⟨NW, _hNW, hw⟩ := WeakPairActivityAsymptotic.uniform_activity C η (3 * ε / 4) hη.le (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NR (max NW NG)), by omega, ?_⟩
  intro N hN L hband
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let T := (zeroFamilies N L).filter fun e ↦ 0 < runRelativeNullity L e
  have hsub : T ⊆ WeakPairActivity.pairs (dyadicBlock N) L η := by
    intro e he
    obtain ⟨he, hdep⟩ := mem_filter.mp he
    obtain ⟨heN, x, y, a, b, rfl, hxy, ha, hb, hcop, hheight, hgeom, hu⟩ := mem_filter.mp he
    have hxN := (mem_powersetCard.mp heN).1 (mem_insert_self x {y})
    have hyN := (mem_powersetCard.mp heN).1 (mem_insert_of_mem (mem_singleton_self y))
    have hrel := relative_le_loss (L := L) (by have h := (mem_Ico.mp hxN).1; omega)
      (by have h := (mem_Ico.mp hyN).1; omega) hxy.ne
    have hloss := (hr N (by omega) L a b x y hband ha hb hcop hheight hxN hyN hgeom).1
    rw [hu] at hloss
    norm_num only [Nat.zero_sub, Nat.cast_zero, zero_add] at hloss
    have hsmall : (runRelativeNullity L {x, y} : ℝ) ≤ η * L := by
      have hrelR : (runRelativeNullity L {x, y} : ℝ) ≤ NormalizedPairRankLoss.pairLoss x y L := by exact_mod_cast hrel
      have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
      have hm := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ η / 2)
      nlinarith only [hrelR, hloss, hm]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨heN, hdep⟩, Or.inl hsmall⟩
  have heq : CompatibleActivitySplit.absolute L (zeroFamilies N L) = CompatibleActivitySplit.absolute L T := by
    symm
    apply sum_subset (filter_subset _ _)
    intro e he hnot
    have hz : runRelativeNullity L e = 0 := Nat.eq_zero_of_not_pos (fun hp ↦ hnot (mem_filter.mpr ⟨he, hp⟩))
    have hne : e.Nonempty := card_pos.mp (by have h := (mem_powersetCard.mp (mem_filter.mp he).1).2; omega)
    rw [AbsoluteActivityDecomposition.centered_zero_direct L hL e hne hz, abs_zero]
  rw [heq]
  calc
    _ ≤ CompatibleActivitySplit.absolute L (WeakPairActivity.pairs (dyadicBlock N) L η) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ abs_nonneg _)
    _ ≤ (N : ℝ) ^ (-1 + η + 3 * ε / 4) := hw N (by omega) L hband (dyadicBlock N) (subset_refl _)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.ZeroUnitAlignedActivity
