module

public import PaperP1.Asymptotics.EnlargedAlignedResidual
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Uniform pair-rank bounds for enlarged alignments, including zero units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedAlignedRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.NormalizedPairRankLoss PaperP1.EnlargedPairGeometry

theorem units_residual_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ (L + 1) ^ 3 → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      Geometric a b x y L →
      (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := EnlargedAlignedResidual.full_rank_sublinear C ε hε
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L a b x y hcrit ha hab hheight hx hy halign
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hx2 : 2 ≤ x := hNtwo.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hNtwo.trans (mem_Ico.mp hy).1
  have hres := hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hheight hx hy halign
  have hfinite : (pairLoss x y L : ℝ) ≤ (((units a b x y L).card - 1 : ℕ) : ℝ) +
      Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast loss_le_units_add_residual_all ha (ha.trans_le hab) hx2 hy2
  linarith

theorem units_channel_bound {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcop : a.Coprime b) (hx : 0 < x) (hy : 0 < y) :
    ((((units a b x y L).card - 1 : ℕ) : ℝ)) ≤ ((L + 1 : ℕ) : ℝ) / b := by
  by_cases hu : 1 ≤ (units a b x y L).card
  · have hcount := intersection_card_bound (L := L) ha hb hcop hx hy
    rw [normalized_intersection_card ha hb hx hy] at hcount
    rw [Nat.cast_sub hu, Nat.cast_one]
    linarith
  · have hu0 : (units a b x y L).card = 0 := by omega
    rw [hu0]
    simp only [Nat.zero_sub, Nat.cast_zero]
    positivity

theorem channel_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → a.Coprime b → b ≤ (L + 1) ^ 3 →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
      (pairLoss x y L : ℝ) ≤ (L : ℝ) / b + ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨Ncore, hcore⟩ := units_residual_bound C (ε / 2) (by positivity)
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (Nat.ceil (2 / ε))
  refine ⟨max Ncore Ngeom, ?_⟩
  intro N hN L a b x y hcrit ha hab hcop hheight hx hy halign
  obtain ⟨hNtwo, hBlarge, _, _, _, _⟩ := hgeom N ((le_max_right _ _).trans hN) L hcrit
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hb : 0 < b := ha.trans_le hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hbound := hcore N ((le_max_left _ _).trans hN) L a b x y hcrit ha hab hheight hx hy halign
  have hcount := units_channel_bound (L := L) ha hb hcop hxpos hypos
  have hceil : 2 / ε ≤ ((Nat.ceil (2 / ε) : ℕ) : ℝ) := Nat.le_ceil _
  have hlarge : 2 / ε ≤ ((L + 1 : ℕ) : ℝ) := hceil.trans (by exact_mod_cast hBlarge)
  have hεB : 2 ≤ ε * ((L + 1 : ℕ) : ℝ) := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith only [h]
  have hinv : 1 / (b : ℝ) ≤ 1 := (div_le_one hbR).mpr hb1
  have hsplit : ((L + 1 : ℕ) : ℝ) / b = (L : ℝ) / b + 1 / b := by push_cast; ring
  rw [hsplit] at hcount
  linarith

end PaperP1.EnlargedAlignedRank
