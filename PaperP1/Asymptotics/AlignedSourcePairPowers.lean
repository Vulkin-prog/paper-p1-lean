module

public import PaperP1.Asymptotics.CriticalPairKernelPowers
public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem

/-! # Uniform raw source weights on enlarged alignments, with no compatibility premise -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedSourcePairPowers

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.NormalizedPairRankLoss
  PaperP1.NormalizedUnitCount PaperP1.EnlargedPairGeometry

theorem uniform_height (b₀ : ℕ) (hb₀ : 0 < b₀) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → 0 < b → a.Coprime b → b₀ ≤ max a b → max a b ≤ (L + 1) ^ 3 →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
        (2 ^ pairLoss x y L : ℝ) ≤ (N : ℝ) ^ (1 / (b₀ : ℝ) + ε) := by
  obtain ⟨NR, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C (1 / (b₀ : ℝ)) 0 ε (by positivity) hε
  refine ⟨max 2 (max NR NP), by omega, ?_⟩
  intro N hN L a b x y hband ha hb hcop hlow hheight hx hy hg
  have hrank := (hr N (by omega) L a b x y hband ha hb hcop hheight hx hy hg).2.1
  have hdiv : (L : ℝ) / max a b ≤ ((L + 1 : ℕ) : ℝ) / b₀ := by
    calc
      _ ≤ (L : ℝ) / b₀ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hb₀)
        (by exact_mod_cast hlow)
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast (show L ≤ L + 1 by omega)) (Nat.cast_nonneg _)
  apply hp N (by omega) L (pairLoss x y L) hband
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) / b₀ + ε / 2 * ((L + 1 : ℕ) : ℝ) :=
      hrank.trans (add_le_add hdiv le_rfl)
    _ = _ := by ring

theorem uniform_zero_units (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → 0 < b → a.Coprime b → max a b ≤ (L + 1) ^ 3 →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → Geometric a b x y L →
      (units a b x y L).card = 0 →
        (2 ^ pairLoss x y L : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NR, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C 0 0 ε (by norm_num) hε
  refine ⟨max 2 (max NR NP), by omega, ?_⟩
  intro N hN L a b x y hband ha hb hcop hheight hx hy hg hu
  have hrank := (hr N (by omega) L a b x y hband ha hb hcop hheight hx hy hg).1
  rw [hu] at hrank
  norm_num only [Nat.zero_sub, Nat.cast_zero, zero_add] at hrank
  simpa only [zero_add, add_zero] using hp N (by omega) L (pairLoss x y L) hband
    (by simpa only [zero_add, add_zero] using hrank)

end PaperP1.AlignedSourcePairPowers
