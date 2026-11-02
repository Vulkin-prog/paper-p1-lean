module

public import PaperP1.Model.ColoredTupleMass
public import PaperP1.Asymptotics.ColoredConditionalSum
public import PaperP1.Combinatorics.TupleExtensions

/-! # Actual one-step propagation of colored tuple mass, uniform in every coloring -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredMassStep

open Finset PaperP1.Arithmetic PaperP1.ColoredPrimeSamples PaperP1.ColoredTupleMass

theorem point_step (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
        (∑ z ∈ Ico N (2 * N), joint M Y L χ c (append x z)) ≤
          (N : ℝ) ^ ε * joint M Y L χ c x := by
  obtain ⟨N₀, hN₀⟩ := ColoredConditionalSum.prescribed_sum s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband κ _ M Y hM χ c x hx
  by_cases hz : joint M Y L χ c x = 0
  · simp only [append_eq_zero M Y L χ c x hz, hz, mul_zero, sum_const_zero, le_refl]
  have hp : 0 < joint M Y L χ c x := lt_of_le_of_ne (joint_nonneg M Y L χ c x) (Ne.symm hz)
  have hsource : 0 < CompatibleSourcePrescriptions.sourceMass
      (ColoredWindowConditional.systems M Y L x 0 (colors s χ)) (fun i ↦ c i.val (x i)) := by
    rw [source_mass_eq]
    exact hp
  have hconditional := hN₀ N hN L hband x hx κ Y M hM (colors s χ) (fun i ↦ c i.val (x i)) hsource (c s)
  calc
    _ = joint M Y L χ c x * ∑ z ∈ Ico N (2 * N), conditional M Y L χ c x z := by
      simp_rw [conditional_factor M Y L χ c x]
      rw [mul_sum]
    _ ≤ joint M Y L χ c x * (N : ℝ) ^ ε := mul_le_mul_of_nonneg_left hconditional hp.le
    _ = _ := mul_comm _ _

theorem family_step (s : ℕ) (hs : 1 ≤ s) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.step (Ico N (2 * N)) F, joint M Y L χ c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint M Y L χ c x := by
  obtain ⟨N₀, hN₀⟩ := point_step s hs C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband κ _ M Y hM χ c F hF
  rw [TupleExtensions.step_sum, mul_sum]
  exact sum_le_sum fun x hx ↦ hN₀ N hN L hband κ M Y hM χ c x (hF x hx)

theorem bounded_orders (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ s : ℕ, 1 ≤ s → s ≤ r →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.step (Ico N (2 * N)) F, joint M Y L χ c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint M Y L χ c x := by
  induction r with
  | zero => exact ⟨0, fun _ _ _ _ s hs hsr ↦ False.elim (by omega)⟩
  | succ r ih =>
    obtain ⟨NI, hNI⟩ := ih
    obtain ⟨NS, hNS⟩ := family_step (r + 1) (by omega) C ε hε
    refine ⟨max NI NS, ?_⟩
    intro N hN L hband s hs hsr κ _ M Y hM χ c F hF
    by_cases hle : s ≤ r
    · exact hNI N (by omega) L hband s hs hle κ M Y hM χ c F hF
    · have heq : s = r + 1 := by omega
      subst s
      exact hNS N (by omega) L hband κ M Y hM χ c F hF

end PaperP1.ColoredMassStep
