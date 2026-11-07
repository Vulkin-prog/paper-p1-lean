module

public import PaperP1.Asymptotics.IndependentTailTheorem

/-! # A full-support tail cutoff fixed before epsilon

For each fixed target exponent a<2, choose an intermediate exponent
strictly between a and 2 and spend part of its margin in the previously
proved estimate. This yields the pure N^-a bound for one cutoff s and
one scale threshold, both independent of any later epsilon.

The theorem retains the original heterogeneous weights and the single
nominal weight of an arbitrary bounded-width block. No endpoint at a=2,
growing block type or new arithmetic input is asserted.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.FixedCutoffIndependentTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_tail (D Q : ℕ) (hD : 1 ≤ D) (hQ : 2 ≤ Q)
    (C v a : ℝ) (hv : 0 < v) (ha : a < 2) :
    ∃ s : ℕ, 3 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      IndependentFullSupportTail.mass (dyadicBlock N) L s v ≤ (N : ℝ)^(-a) ∧
      (∀ U : ℕ → Finset ℕ,
        (∀ x ∈ Ico 2 (Q*N+2), U x ⊆ NormalizedWindowSets.values x (D*(L+1))) →
        BoundedBlockIndependentTail.mass Q N L (s-1) v U ≤ (N : ℝ)^(-a)) := by
  obtain ⟨s,hs,N₀,hN₀,h⟩ := IndependentTailTheorem.article_15_8 D Q hD hQ C v
    ((a+2)/2) ((2-a)/4) hv (by linarith) (by linarith)
  refine ⟨s,hs,N₀,hN₀,?_⟩
  intro N hN L hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ)^(-((a+2)/2)+(2-a)/4) ≤ (N : ℝ)^(-a) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  obtain ⟨ho,hb⟩ := h N hN L hband
  exact ⟨ho.trans hpower,fun U hU ↦ (hb U hU).trans hpower⟩

theorem article_15_8_fixed_cutoff (D Q : ℕ) (hD : 1 ≤ D) (hQ : 2 ≤ Q)
    (C v a : ℝ) (hv : 0 < v) (ha : a < 2) :
    ∃ s : ℕ, 3 ≤ s ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, 10 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ L : ℕ, |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      IndependentFullSupportTail.mass (dyadicBlock N) L s v ≤ (N : ℝ)^(-a+ε) ∧
      (∀ U : ℕ → Finset ℕ,
        (∀ x ∈ Ico 2 (Q*N+2), U x ⊆ NormalizedWindowSets.values x (D*(L+1))) →
        BoundedBlockIndependentTail.mass Q N L (s-1) v U ≤ (N : ℝ)^(-a+ε)) := by
  obtain ⟨s,hs,N₀,hN₀,h⟩ := uniform_tail D Q hD hQ C v a hv ha
  refine ⟨s,hs,?_⟩
  intro ε hε
  refine ⟨N₀,hN₀,?_⟩
  intro N hN L hband
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpower : (N : ℝ)^(-a) ≤ (N : ℝ)^(-a+ε) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  obtain ⟨ho,hb⟩ := h N hN L hband
  exact ⟨ho.trans hpower,fun U hU ↦ (hb U hU).trans hpower⟩

end PaperP1.FixedCutoffIndependentTail
