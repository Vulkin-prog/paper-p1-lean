module

public import PaperP1.Asymptotics.PrescribedSplitProductCount

/-! # Exact homogeneous power form of the actual prescribed split-product count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitProductPowerForm

open Finset PaperP1.SplitOffsetProducts PaperP1.SelectedQuadraticCells

def profile (d : ℕ) (Q : ℝ) (e : ℕ) : ℝ := Q ^ (1 / (2 * d : ℝ)) / (e : ℝ) ^ (1 / (d : ℝ))

theorem profile_pos (d e : ℕ) (Q : ℝ) (he : 0 < e) (hQ : 0 < Q) : 0 < profile d Q e := by
  unfold profile
  exact div_pos (Real.rpow_pos_of_pos hQ _) (Real.rpow_pos_of_pos (by exact_mod_cast he) _)

theorem power_identity (N d e : ℕ) (Q α : ℝ) (hN : 2 ≤ N) (hd : 2 ≤ d) (he : 0 < e) (hQ : 0 < Q) :
    (N : ℝ) ^ (baseExponent d (Real.log Q / Real.log N) (Real.log e / Real.log N) + α) =
      (N : ℝ) ^ (1 / 2 + α) * profile d Q e := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  unfold profile
  simp only [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hQ, Real.rpow_def_of_pos heR]
  rw [← Real.exp_sub, ← Real.exp_add]
  congr 1
  unfold baseExponent
  field_simp
  ring

theorem uniform_prescribed_power_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ Q : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → 0 < e → 0 < Q →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ e ∣ kernel A n ∧ (kernel A n : ℝ) ≤ Q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + c * Real.log 2 + ε) * profile A.card Q e := by
  obtain ⟨Nc, hNc⟩ := PaperP1.PrescribedSplitProductCount.cumulative_count c D A₀ ε hc hε
  refine ⟨max 2 Nc, ?_⟩
  intro N hN W e A Q hW heven hcard hwidth hdegree hA he hQ S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (N : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast (show 1 < N by omega))
  have hQeq : (N : ℝ) ^ (Real.log Q / Real.log N) = Q := Real.rpow_logb hn hn1 hQ
  have hcount := hNc N (by omega) W e A (Real.log Q / Real.log N) hW heven hcard hwidth hdegree hA S (by
    intro n hnS
    obtain ⟨hnlo, hnhi, hediv, hupper⟩ := hS n hnS
    exact ⟨hnlo, hnhi, hediv, by rwa [hQeq]⟩)
  rw [add_assoc] at hcount
  rw [power_identity N A.card e Q (c * Real.log 2 + ε) (by omega) hcard he hQ] at hcount
  simpa only [add_assoc] using hcount

end PaperP1.SplitProductPowerForm
