module

public import PaperP1.Asymptotics.TwoTargetPureClassData

/-! # Two actual pure classes in each target give an unconditional subpower pair count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetPureCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassOffsets PaperP1.TwoTargetPrimeClassSupports
  PaperP1.TwoTargetMixedClassData PaperP1.CriticalCoefficientPatterns PaperP1.DisjointRecoverySubspace

local instance pureCountPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem uniform_pairs (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
      ∀ F : Finset (ℕ × ℕ), (∀ p ∈ F, p.1 ∈ dyadicBlock N ∧ p.2 ∈ dyadicBlock N) →
        (∀ p ∈ F, ∃ M : Submodule F₂ (code (starts x p.1 p.2) L),
          NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x p.1 p.2) L)) M (s + 1) t ∧
          ∀ j : Fin 2, ∃ α : Fin 2 → Module.Dual F₂ M, Function.Injective α ∧ (∀ i, α i ≠ 0) ∧
            ∀ i : Fin 2,
              (targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j).Nonempty ∧
                targetOffsets (LabelClassPartition.part (label (starts x p.1 p.2) M) (α i)) j.rev = ∅) →
        (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nc, _hNc, hcount⟩ := CoefficientUnivariateCount.uniform_pairs C ε (t - 1) hε
  obtain ⟨Ne, _hNe, henumerate⟩ := TwoTargetPureClassData.uniform_systems s t ht D C
    (coefficientMargin (ε / 4) 2) hD (margin_pos (by positivity) 2)
  refine ⟨max Ne Nc, by omega, ?_⟩
  intro N hN L H hband hHlo hHhi x hx F hdyadic hclasses
  obtain ⟨hcard, hsystems⟩ := henumerate N (by omega) L H hband hHlo hHhi x hx
  apply hcount N (by omega) L hband (boundedCoefficients x L H t N) hcard
    (fun d hd ↦ (bounded_coefficient x L H t N d hd).1) F hdyadic
  intro p hp
  obtain ⟨M, hno, hpure⟩ := hclasses p hp
  have h (j : Fin 2) : CoefficientUnivariateCount.HasSystem L (t - 1) (boundedCoefficients x L H t N)
      (if j = 0 then p.1 else p.2) := by
    obtain ⟨α, hinj, hnonzero, hpure⟩ := hpure j
    exact hsystems p.1 p.2 (hdyadic p hp).1 (hdyadic p hp).2 M hno j α hinj hnonzero hpure
  exact ⟨by simpa only [ite_true] using h 0,
    by simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using h 1⟩

end PaperP1.TwoTargetPureCount
