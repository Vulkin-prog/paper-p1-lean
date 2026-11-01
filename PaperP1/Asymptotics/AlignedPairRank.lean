module

public import PaperP1.Asymptotics.NormalizedPairResidual
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # The uniform o(B) rank bound of T1.9 on actual normalized aligned pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPairRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.CriticalBandScale

theorem units_residual_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      (units a b x y L).Nonempty →
      (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := NormalizedPairResidual.rank_sublinear C ε hε
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hab hheight hx hy hunits
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hxN := (mem_Ico.mp hx).1
  have hyN := (mem_Ico.mp hy).1
  have hx2 : 2 ≤ x := hNtwo.trans hxN
  have hy2 : 2 ≤ y := hNtwo.trans hyN
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨u, hu⟩ := hunits
  have hres := hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hheight hxN
    (by omega : 0 < y) u.1 u.2 (mem_units.mp hu)
  have hfinite : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
      Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast loss_le_units_add_residual ha hb hx2 hy2 ⟨u, hu⟩
  norm_num only [Nat.cast_add, Nat.cast_one] at hres ⊢
  linarith

theorem channel_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
      (pairLoss x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := units_residual_bound C (ε / 2) (by positivity)
  obtain ⟨Nscale, hscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hlog⟩ := ElementaryLogGrowth.log_ge_eventually ((2 / ε) / lowerScale)
  refine ⟨max Ncore (max Nscale (max Nlog 2)), ?_⟩
  intro N hN L a b x y hcrit ha hab hcop hheight hx hy hunits
  have hNtwo : 2 ≤ N := (le_max_right Nlog 2).trans ((le_max_right Nscale _).trans ((le_max_right _ _).trans hN))
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hb : 0 < b := ha.trans_le hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbound := hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hheight hx hy hunits
  have hcount := intersection_card_bound (L := L) ha hb hcop hxpos hypos
  rw [normalized_intersection_card ha hb hxpos hypos] at hcount
  have hu : 1 ≤ (units a b x y L).card := hunits.card_pos
  rw [Nat.cast_sub hu, Nat.cast_one] at hbound
  have hscaleN := (hscale N ((le_max_left Nscale _).trans ((le_max_right _ _).trans hN)) L hcrit).1
  have hlogN := (hlog N ((le_max_left Nlog 2).trans ((le_max_right Nscale _).trans ((le_max_right _ _).trans hN)))).1
  have hlarge : 2 / ε ≤ ((L + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ lowerScale_pos).mp hlogN
    nlinarith only [h, hscaleN]
  have hεB : 2 ≤ ε * ((L + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith only [h]
  have hinv : 1 / (b : ℝ) ≤ 1 := (div_le_one hbR).mpr hb1
  have hsplit : ((L + 1 : ℕ) : ℝ) / b = (L : ℝ) / b + 1 / b := by push_cast; ring
  rw [hsplit] at hcount
  linarith

theorem actual_intersection_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → (units a b x y L).Nonempty →
      (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := channel_bound C ε hε
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hab hcop hheight hx hy hunits
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; have := (le_max_right _ _).trans hN; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; have := (le_max_right _ _).trans hN; omega
  have hinter : (FreeComponentRank.pairIntersectionRank x y L : ℝ) ≤ pairLoss x y L := by
    exact_mod_cast intersection_rank_le_loss hxpos hypos
  exact hinter.trans (hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hcop hheight hx hy hunits)

end PaperP1.AlignedPairRank
