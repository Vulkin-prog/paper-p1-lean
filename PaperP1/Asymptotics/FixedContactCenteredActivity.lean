module

public import PaperP1.Asymptotics.ContactSeedKernel
public import PaperP1.Asymptotics.SubpowerShiftedCountMoments

/-! # Unconditional N^(-1+epsilon) centered contact activity at every fixed order

Only subpower fixed moments are needed. The cutoff and the higher moment
order are selected after r,epsilon and before N. No BCN estimate, growing
order theorem or uniform bounded-moment premise is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedContactCenteredActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ContactCenteredTruncation

theorem uniform_bound (r : ℕ) (hr : 2 ≤ r) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      CompatibleActivitySplit.absolute L (families G L r) ≤ (N : ℝ) ^ (-1 + ε) := by
  let δ := ε / (4 * ((r + 1 : ℕ) : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨k, hk⟩ := exists_nat_ge ((1 + δ) / δ)
  have hdk : 1 + δ ≤ δ * k := by
    have h := (div_le_iff₀ hδ).mp hk
    linarith only [h]
  let m := r + k
  have hm : r ≤ m := by dsimp [m]; omega
  obtain ⟨NS, _hNS, hs⟩ := ContactSeedKernel.uniform_kernel C δ hδ
  obtain ⟨NM, _hNM, hmom⟩ := SubpowerShiftedCountMoments.uniform_bound m C δ hδ
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NS (max NM NF)), by omega, ?_⟩
  intro N hN L hband G hG
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R := (N : ℝ) ^ δ
  have hR : 0 < R := Real.rpow_pos_of_pos hn _
  have hp (j : ℕ) : R ^ j = (N : ℝ) ^ (δ * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have hden : δ * (4 * ((r + 1 : ℕ) : ℝ)) = ε := by
    dsimp [δ]
    exact div_mul_cancel₀ _ (by positivity)
  have hcount : ((r - 2 : ℕ) : ℝ) + 1 ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show r - 2 + 1 ≤ r + 1 by omega)
  have hbudget := mul_le_mul_of_nonneg_left hcount hδ.le
  have hfirst : R ^ (r - 2) * (N : ℝ) ^ (-1 + δ) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    rw [hp, ← Real.rpow_add hn]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hden, hbudget, hε])
  have hsecond : (N : ℝ) ^ δ / R ^ (m - r) ≤ (N : ℝ) ^ (-1 + ε / 2) := by
    rw [show m - r = k by dsimp [m]; omega, hp, ← Real.rpow_sub hn]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hdk, hε])
  have hfinite := ContactCenteredTruncation.finite_bound (L := L) hG r hr R hR m hm
  have hkernel := hs N (by omega) L hband G hG
  have hmoment := hmom N (by omega) L hband G hG
  calc
    _ ≤ R ^ (r - 2) * (N : ℝ) ^ (-1 + δ) + (N : ℝ) ^ δ / R ^ (m - r) :=
      hfinite.trans (add_le_add
        (mul_le_mul_of_nonneg_left hkernel (by positivity))
        (div_le_div_of_nonneg_right hmoment (by positivity)))
    _ ≤ 2 * (N : ℝ) ^ (-1 + ε / 2) := by linarith only [hfirst, hsecond]
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FixedContactCenteredActivity
