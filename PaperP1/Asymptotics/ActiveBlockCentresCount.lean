module

public import PaperP1.Arithmetic.DependentBlockPairs
public import PaperP1.Asymptotics.BlockCentreHeights
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Active candidate centres are counted from actual block value heights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActiveBlockCentresCount

open Finset PaperP1.EffectiveWindowLists PaperP1.BlockCentreHeights PaperP1.DependentBlockPairs

theorem uniform_count (a b D Cband ε : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ G : Finset ℕ, ∀ block : ℕ → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (∀ x ∈ G, ∀ v ∈ block x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ x ∈ G, ∀ v ∈ block x, (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((active G block).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  classical
  obtain ⟨C, hC⟩ := exists_nat_ge (upper b)
  obtain ⟨NC, hNC⟩ := PaperP1.HalfCountSchedule.centre_count C ε hε
  obtain ⟨NB, hNB⟩ := radius_logarithmic D Cband hD
  obtain ⟨NW, hNW⟩ := logarithmic_radius a (D * PaperP1.CriticalBandScale.upperScale + 2) ha
  refine ⟨max NC (max NB NW), ?_⟩
  intro N hN L G block hband hvalues hdist
  let W := radius D L
  have hW := hNW N (by omega) W (hNB N (by omega) L hband)
  apply hNC N (by omega) (active G block)
  intro x hx
  obtain ⟨hxG, hxspace⟩ := mem_filter.mp hx
  obtain ⟨u, hu, hne⟩ := (Submodule.ne_bot_iff _).mp hxspace
  obtain ⟨v, hv⟩ := effective_nonempty (block x) u hu hne
  have hcentre := centre_bounds a b N W x v (hvalues x hxG v hv)
    (distance_le_radius D L _ (hdist x hxG v hv)) hW.1 hW.2
  have hbound : (x : ℝ) ≤ C * N := hcentre.2.trans
    (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N))
  exact_mod_cast hbound

end PaperP1.ActiveBlockCentresCount
