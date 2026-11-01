module

public import PaperP1.Asymptotics.FixedSourceMassStep
public import PaperP1.Model.TupleMassIteration
public import PaperP1.Model.PrescribedRunMass

/-! # Actual fixed-order extension mass grows by at most an arbitrary subpower -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedOrderMassPropagation

open Finset PaperP1.Arithmetic PaperP1.PrescribedTupleMass

theorem all_extensions (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.more (Ico N (2 * N)) F k, joint L c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  let δ := ε / (k + 1 : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NS, hNS⟩ := FixedSourceMassStep.bounded_orders (s + k) C δ hδ
  refine ⟨max NS 1, ?_⟩
  intro N hN L hband c F hF
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hstep := hNS N (by omega) L hband
  have hfinite := TupleMassIteration.iterate (Ico N (2 * N)) c ((N : ℝ) ^ δ) hs
    (Real.rpow_nonneg hNr.le _) (fun q hq hqr F hF ↦ hstep q hq hqr c F hF) F hF k le_rfl
  have hexponent : δ * (k : ℝ) ≤ ε := by
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < k + 1)).mpr
    nlinarith only [hε]
  calc
    _ ≤ _ := hfinite
    _ = (N : ℝ) ^ (δ * (k : ℝ)) * ∑ x ∈ F, joint L c x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1 hexponent)
      (sum_nonneg (fun x _ ↦ joint_nonneg c x))

/-- Every subfamily of the actual extensions, in particular the ordered
distinct extensions of a family of ordered distinct source tuples. -/
theorem extension_subfamilies (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ T : Finset (Fin (s + k) → ℕ), T ⊆ TupleExtensions.more (Ico N (2 * N)) F k →
        (∑ y ∈ T, joint L c y) ≤ (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  obtain ⟨N₀, hN₀⟩ := all_extensions s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband c F hF T hT
  exact (sum_le_sum_of_subset_of_nonneg hT (fun y _ _ ↦ joint_nonneg c y)).trans
    (hN₀ N hN L hband c F hF)

/-- The actual ordered-distinct extension-family assertion of main 6.3. -/
theorem main_6_3_propagation (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ c : ℕ → Fin L → F₂,
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.distinctMore (Ico N (2 * N)) F k, joint L c y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, joint L c x := by
  obtain ⟨N₀, hN₀⟩ := extension_subfamilies s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband c F hF
  exact hN₀ N hN L hband c F hF _ (filter_subset _ _)

theorem original_run_extensions (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (Fin s → ℕ), (∀ x ∈ F, ∀ i, x i ∈ Ico N (2 * N)) →
        (∑ y ∈ TupleExtensions.distinctMore (Ico N (2 * N)) F k,
          Model.InfiniteStarts.infiniteFamilyJointMoment L y) ≤
          (N : ℝ) ^ ε * ∑ x ∈ F, Model.InfiniteStarts.infiniteFamilyJointMoment L x := by
  obtain ⟨N₀, hN₀⟩ := main_6_3_propagation s hs k C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hL hband F hF
  have h := hN₀ N hN L hband (fun _ ↦ Affine.startRhs L) F hF
  simpa only [PrescribedRunMass.joint_eq_infinite _ hL] using h

end PaperP1.FixedOrderMassPropagation
