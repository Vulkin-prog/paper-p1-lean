module

public import PaperP1.Asymptotics.GeneralWindowBranching
public import PaperP1.Asymptotics.FixedWindowBranching
public import PaperP1.Arithmetic.BranchingPatterns

/-! # Companion T1.15 with subsets, fixed dilations, enlarged windows and original observations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralBranchingTheorem

open Finset MeasureTheory ProbabilityTheory PaperP1.Arithmetic PaperP1.Model
  PaperP1.GeneralWindowBranching PaperP1.BranchingPatterns PaperP1.SelectedRelativeBits
  PaperP1.ConditionalRelativeBits PaperP1.RelativeSignIndependence PaperP1.FixedWindowBranching
  PaperP1.OldPrimeCardinality PaperP1.Model.InfiniteRademacher

local instance generalBranchingMeasurableF2 : MeasurableSpace F₂ := ⊤

def ReindexedConclusion {ι : Type*} (G : Finset ι) (φ : ι → ℕ) (R : Finset ℕ) (L : ℕ) (E : Finset ι) : Prop :=
  ∀ z ∈ G, z ∉ E →
    infiniteRademacherMeasure.map (infiniteStartBits (φ z) L) = Measure.pi (fun _ : Fin L ↦ coordinateMeasure) ∧
    IndepFun (infiniteStartBits (φ z) L) (infiniteOldBits R) infiniteRademacherMeasure ∧
    ∀ (k : ℕ) (g : Fin (k + 1) → Fin (L + 1)), Function.Injective g →
      infiniteRademacherMeasure.map (selectedBits (φ z) L g) = Measure.pi (fun _ : Fin k ↦ coordinateMeasure) ∧
      IndepFun (selectedBits (φ z) L g) (infiniteOldBits R) infiniteRademacherMeasure

theorem reindexed_windows (K : ℕ) (hK : 1 ≤ K) (D : ℝ) (hD : 0 ≤ D) (j : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ {ι : Type*} (G : Finset ι) (R : Finset ℕ) (φ : ι → ℕ), Set.InjOn φ G →
        (∀ z ∈ G, 2 ≤ φ z) → (∀ z ∈ G, φ z + L ≤ K * N) →
        (∀ n ∈ R, 1 ≤ n ∧ n ≤ K * N) → R.card ≤ j * (L + 1) →
          ∃ E : Finset ι, E ⊆ G ∧ (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧ ReindexedConclusion G φ R L E := by
  obtain ⟨N₀, hN₀, hbase⟩ := bounded_height_windows K hK D hD j ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hwidth ι G R φ hφ hlo hhi hR hcard
  have hlo' : ∀ x ∈ G.image φ, 2 ≤ x := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    exact hlo z hz
  have hhi' : ∀ x ∈ G.image φ, x + L ≤ K * N := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hx
    exact hhi z hz
  obtain ⟨F, _, hFcount, hind⟩ := hbase N hN L hwidth (G.image φ) R hlo' hhi' hR hcard
  refine ⟨pullExceptions G φ F, pullExceptions_subset _ _ _, ?_, ?_⟩
  · have hcount : ((pullExceptions G φ F).card : ℝ) ≤ F.card := by exact_mod_cast pullExceptions_card G φ F hφ
    exact hcount.trans hFcount
  · intro z hz hnot
    exact hind (φ z) (mem_image_of_mem φ hz) (notMem_pullExceptions hz hnot)

theorem dilation_conclusion {ι : Type*} {G E : Finset ι} {φ : ι → ℕ} {R : Finset ℕ} {L : ℕ}
    (h : ReindexedConclusion G φ R L E) {z : ι} (hz : z ∈ G) (hnot : z ∉ E)
    (k a d : ℕ) (hd : 0 < d) (hfit : a + d * k ≤ L) :
    infiniteRademacherMeasure.map (selectedBits (φ z) L (dilationIndices a d hfit)) =
        Measure.pi (fun _ : Fin k ↦ coordinateMeasure) ∧
      IndepFun (selectedBits (φ z) L (dilationIndices a d hfit)) (infiniteOldBits R) infiniteRademacherMeasure :=
  (h z hz hnot).2.2 k _ (dilationIndices_injective a d hd hfit)

/-- Both the original literal bound and the full generalized-window clause. -/
theorem companion_T1_15 (C : ℝ) (K : ℕ) (hK : 1 ≤ K) (D : ℝ) (hD : 0 ≤ D)
    (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀,
      (∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        ∀ A : Finset ℕ, A ⊆ dyadicBlock N → A.card ≤ j →
          ∃ E : Finset ℕ, E ⊆ dyadicBlock N ∧ IndependentConclusion N L A E ∧
            (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧
            (E.card : ℝ) ≤ (j : ℝ) * (2 * L + 1) + ((L + 1 : ℕ) : ℝ) * Real.sqrt (3 * N : ℕ) *
              Real.exp (2 * Real.sqrt (primeCountBudget N L j))) ∧
      (∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
        ∀ (G R : Finset ℕ) (φ : ℕ → ℕ), Set.InjOn φ G →
          (∀ z ∈ G, 2 ≤ φ z) → (∀ z ∈ G, φ z + L ≤ K * N) →
          (∀ n ∈ R, 1 ≤ n ∧ n ≤ K * N) → R.card ≤ j * (L + 1) →
            ∃ E : Finset ℕ, E ⊆ G ∧ (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧ ReindexedConclusion G φ R L E) := by
  obtain ⟨Noriginal, hNoriginal, horiginal⟩ := original_windows_critical C j ε hε
  obtain ⟨Ngeneral, _, hgeneral⟩ := reindexed_windows K hK D hD j ε hε
  refine ⟨max Noriginal Ngeneral, by omega, fun N hN ↦ ?_⟩
  exact ⟨fun L hband A hA hj ↦ horiginal N (by omega) L hband A hA hj,
    fun L hwidth G R φ hφ hlo hhi hR hcard ↦ hgeneral N (by omega) L hwidth G R φ hφ hlo hhi hR hcard⟩

end PaperP1.GeneralBranchingTheorem
