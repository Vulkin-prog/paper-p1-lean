module

public import PaperP1.Asymptotics.MacroscopicEnlargedAlignedRank
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # Uniform powers of the actual macroscopic relation loss

Moving reduced heights and both coefficient orientations follow the common
threshold. No homogeneous-probability or nominal-mean substitution is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicRelationPowers

open PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedUnitCount
  PaperP1.NormalizedPairRankLoss PaperP1.EnlargedPairGeometry PaperP1.MacroscopicIntervalGeometry

theorem uniform_channel (C δ : ℝ) (hδ : 0 < δ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → a.Coprime b →
      q ≤ b → b ≤ (L + 1) ^ 3 → x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (2 ^ pairLoss x y L : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ) + ε) := by
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicEnlargedAlignedRank.channel_bound C δ (ε / 2) hδ (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.CriticalPairKernelPowers.power_of_rank C (1 / (q : ℝ)) 0 ε (by positivity) hε
  refine ⟨max MR MP, ?_⟩
  intro M hM L a b x y hcrit ha hab hcop hqb hheight hx hy hg
  have hloss := hR M (by omega) L a b x y hcrit ha hab hcop hheight hx hy hg
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hq.trans_le hqb
  have hfrac : (L : ℝ) / b ≤ ((L + 1 : ℕ) : ℝ) / q := by
    apply (div_le_div_iff₀ hbR hqR).mpr
    exact mul_le_mul (by exact_mod_cast Nat.le_succ L) (by exact_mod_cast hqb)
      (Nat.cast_nonneg q) (Nat.cast_nonneg (L + 1))
  apply hP M (by omega) L (pairLoss x y L) hcrit
  calc
    _ ≤ (L : ℝ) / b + (ε / 2) * ((L + 1 : ℕ) : ℝ) := hloss
    _ ≤ ((L + 1 : ℕ) : ℝ) / q + (ε / 2) * ((L + 1 : ℕ) : ℝ) := add_le_add hfrac le_rfl
    _ = (1 / (q : ℝ) + ε / 2) * ((L + 1 : ℕ) : ℝ) + 0 := by ring

theorem uniform_height (C δ : ℝ) (hδ : 0 < δ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → 0 < b → a.Coprime b →
      q ≤ max a b → a ≤ (L + 1) ^ 3 → b ≤ (L + 1) ^ 3 →
      x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (2 ^ pairLoss x y L : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := uniform_channel C δ hδ q hq ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hb hcop hqmax haB hbB hx hy hg
  by_cases hab : a ≤ b
  · have hqb : q ≤ b := by simpa only [max_eq_right hab] using hqmax
    exact h M hM L a b x y hcrit ha hab hcop hqb hbB hx hy hg
  · have hba : b ≤ a := by omega
    have hqa : q ≤ a := by simpa only [max_eq_left hba] using hqmax
    have hs := h M hM L b a y x hcrit hb hba hcop.symm hqa haB hy hx ((geometric_swap a b x y L).mp hg)
    simpa only [pairLoss_comm y x L] using hs

theorem uniform_no_units (C δ : ℝ) (hδ : 0 < δ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → a ≤ b → b ≤ (L + 1) ^ 3 →
      x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L → (units a b x y L).card = 0 →
      (2 ^ pairLoss x y L : ℝ) ≤ (M : ℝ) ^ ε := by
  obtain ⟨MR, hR⟩ := PaperP1.MacroscopicEnlargedAlignedRank.units_residual_bound C δ (ε / 2) hδ (by positivity)
  obtain ⟨MP, hP⟩ := PaperP1.CriticalPairKernelPowers.power_of_rank C 0 0 ε (by norm_num) hε
  refine ⟨max MR MP, ?_⟩
  intro M hM L a b x y hcrit ha hab hheight hx hy hg hz
  have hloss := hR M (by omega) L a b x y hcrit ha hab hheight hx hy hg
  have hrank : (pairLoss x y L : ℝ) ≤ (0 + ε / 2) * ((L + 1 : ℕ) : ℝ) + 0 := by
    simpa only [hz, Nat.zero_sub, Nat.cast_zero, zero_add, add_zero] using hloss
  simpa only [zero_add] using hP M (by omega) L (pairLoss x y L) hcrit hrank

theorem uniform_rational_units (C : ℝ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → 0 < b → a.Coprime b → q ≤ b →
      0 < x → 0 < y →
      (2 ^ ((units a b x y L).card - 1) : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := PaperP1.CriticalPairKernelPowers.power_of_rank C (1 / (q : ℝ)) 0 ε (by positivity) hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hb hcop hqb hx hy
  have hcount := PaperP1.EnlargedAlignedRank.units_channel_bound (L := L) ha hb hcop hx hy
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hfrac : ((L + 1 : ℕ) : ℝ) / b ≤ ((L + 1 : ℕ) : ℝ) / q := by
    apply (div_le_div_iff₀ hbR hqR).mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hqb) (Nat.cast_nonneg (L + 1))
  apply h M (by omega) L ((units a b x y L).card - 1) hcrit
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) / b := hcount
    _ ≤ ((L + 1 : ℕ) : ℝ) / q := hfrac
    _ = (1 / (q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ (1 / (q : ℝ)) * ((L + 1 : ℕ) : ℝ) + (ε / 2) * ((L + 1 : ℕ) : ℝ) :=
      le_add_of_nonneg_right (by positivity)
    _ = (1 / (q : ℝ) + ε / 2) * ((L + 1 : ℕ) : ℝ) + 0 := by ring

theorem uniform_rational_height (C : ℝ) (q : ℕ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C → 0 < a → 0 < b → a.Coprime b →
      q ≤ max a b → 0 < x → 0 < y →
      (2 ^ ((units a b x y L).card - 1) : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ) + ε) := by
  obtain ⟨M₀, h⟩ := uniform_rational_units C q hq ε hε
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hb hcop hqmax hx hy
  by_cases hab : a ≤ b
  · exact h M hM L a b x y hcrit ha hb hcop (by simpa only [max_eq_right hab] using hqmax) hx hy
  · have hba : b ≤ a := by omega
    have hs := h M hM L b a y x hcrit hb ha hcop.symm (by simpa only [max_eq_left hba] using hqmax) hy hx
    rw [← units_card_swap ha hb hx hy] at hs
    exact hs

end PaperP1.MacroscopicRelationPowers
