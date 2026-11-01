module

public import PaperP1.Asymptotics.HalfCountStages

/-! # Every surviving long source enters the actual deterministic exceptional set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountStageConfinement

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountStages PaperP1.HalfCountExceptionalSets PaperP1.BoundedIntegerMotifs

theorem uniform_confinement (a b A E ε : ℝ) (ha : 0 < a) (hA : 2 ≤ A)
    (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ M : ℕ → Finset ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((M N).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) ∧
      ∀ W t r s : ℕ, ∀ old : Fin s → ℕ, ∀ j : ℕ, ∀ Y : ℕ → ℝ, ∀ G : Finset ℕ,
        (W : ℝ) ≤ E * Real.log N → (∀ x ∈ G, a * N ≤ x ∧ (x : ℝ) ≤ b * N) →
        Y j = (Real.log N) ^ A →
        ∀ n ∈ survivors (r := r) G N W old (t + 25) t Y (j + 1), ∀ i,
          t + 25 < (chosen W old n i).card → n i ∈ M N ∩ G := by
  classical
  obtain ⟨M, N₀, hN₀⟩ := stage_confinement a b A E ε ha hA hE hε
  refine ⟨M, N₀, ?_⟩
  intro N hN
  refine ⟨(hN₀ N hN).1, ?_⟩
  intro W t r s old j Y G hwidth hG hY n hn i hi
  obtain ⟨hnL, _, houtside⟩ := survivor_data G N W old (t + 25) t (j + 1) Y n hn
  have hnG := ((mem_lists G W old n).mp hnL).1 i
  have hA := chosen_spec G W old n hnL
  have hfew := survivor_few_large G N W old (t + 25) t j Y n hn i hi
  rw [hY] at hfew
  have hmem := (hN₀ N hN).2 W t (n i) G (chosen W old n i) hwidth hG hnG
    (houtside i) ((subset_offsets W _).mp (hA.1 i).2.1) (by omega) hfew
  exact mem_inter.mpr ⟨hmem, hnG⟩

end PaperP1.HalfCountStageConfinement
