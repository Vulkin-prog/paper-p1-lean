module

public import PaperP1.Asymptotics.ColoredMassStep
public import PaperP1.Model.ColoredWeightedIteration

/-! # Uniform fixed-order colored propagation with every seed weight retained -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ColoredMassPropagation

open Finset PaperP1.Arithmetic PaperP1.ColoredTupleMass

theorem bounded_point_orders (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ s : ℕ, 1 ≤ s → s ≤ r →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ Ico N (2 * N)) →
        (∑ z ∈ Ico N (2 * N), joint M Y L χ c (append x z)) ≤
          (N : ℝ) ^ ε * joint M Y L χ c x := by
  obtain ⟨N₀, hN₀⟩ := ColoredMassStep.bounded_orders r C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband s hs hsr κ _ M Y hM χ c x hx
  have h := hN₀ N hN L hband s hs hsr κ M Y hM χ c {x}
    (fun y hy ↦ by simpa only [mem_singleton.mp hy] using hx)
  simpa only [TupleExtensions.step_sum, sum_singleton] using h

theorem weighted_extensions (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ a : (Fin s → ℕ) → ℝ, (∀ x, 0 ≤ a x) →
        (∑ y ∈ TupleExtensions.more (Ico N (2 * N)) F k,
          a (TupleExtensions.initial k y) * joint M Y L χ c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, a x * joint M Y L χ c x := by
  let δ := ε / (k + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NS, hNS⟩ := bounded_point_orders (s + k) C δ hδ
  refine ⟨max NS 1, ?_⟩
  intro N hN L hband κ _ M Y hM χ c F hF a ha
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hfinite := ColoredWeightedIteration.iterate (Ico N (2 * N)) χ c ((N : ℝ) ^ δ) hs
    (Real.rpow_nonneg hNr.le _)
    (fun q hq hqr x hx ↦ hNS N (by omega) L hband q hq hqr κ M Y hM χ c x hx)
    F hF a ha k le_rfl
  have hexponent : δ * (k : ℝ) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
    nlinarith only [hε]
  calc
    _ ≤ _ := hfinite
    _ = (N : ℝ) ^ (δ * (k : ℝ)) * ∑ x ∈ F, a x * joint M Y L χ c x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hexponent)
      (sum_nonneg (fun x _ ↦ mul_nonneg (ha x) (joint_nonneg M Y L χ c x)))

theorem weighted_subfamilies (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ χ : ℕ → κ, ∀ c : ℕ → ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ a : (Fin s → ℕ) → ℝ, (∀ x, 0 ≤ a x) →
      ∀ T : Finset (Fin (s + k) → ℕ), T ⊆ TupleExtensions.more (Ico N (2 * N)) F k →
        (∑ y ∈ T, a (TupleExtensions.initial k y) * joint M Y L χ c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, a x * joint M Y L χ c x := by
  obtain ⟨N₀, hN₀⟩ := weighted_extensions s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband κ _ M Y hM χ c F hF a ha T hT
  exact (sum_le_sum_of_subset_of_nonneg hT
    (fun y _ _ ↦ mul_nonneg (ha _) (joint_nonneg M Y L χ c y))).trans
      (hN₀ N hN L hband κ M Y hM χ c F hF a ha)

end PaperP1.ColoredMassPropagation
