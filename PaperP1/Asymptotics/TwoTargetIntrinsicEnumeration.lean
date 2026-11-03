module

public import PaperP1.Asymptotics.TwoTargetCoefficientEnumeration
public import PaperP1.Arithmetic.TwoTargetIntrinsicClassCoefficients
public import PaperP1.Arithmetic.TwoTargetClassCoefficients
public import PaperP1.Arithmetic.TwoTargetWindowSections
public import PaperP1.Arithmetic.OriginalWindowValueBounds

/-! # The common actual two-target coefficient list only requires intrinsic recovery exclusion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoTargetIntrinsicEnumeration

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations PaperP1.Model
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetClassCoefficients PaperP1.TwoTargetClassSourceCover
  PaperP1.TwoTargetPrimeClassSupports PaperP1.DisjointRecoveryTheorem PaperP1.SmallPrimeBudget
  PaperP1.TwoTargetCoefficientEnumeration

local instance twoTargetEnumerationTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (M : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ M) := Classical.decEq _

theorem uniform_enumeration (s t : ℕ) (ht : 2 ≤ t) (D C ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → L + 1 ≤ H → (H : ℝ) ≤ D * (L + 1 : ℕ) →
      ∀ x : Fin s → ℕ, (∀ i, x i ∈ dyadicBlock N) →
        ((coefficients x L H t).card : ℝ) ≤ (N : ℝ) ^ ε ∧
        ∀ y z : ℕ, y ∈ dyadicBlock N → z ∈ dyadicBlock N →
        ∀ M : Submodule F₂ (code (starts x y z) L),
          DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) M (s + 1) t →
        ∀ α : Module.Dual F₂ M, α ≠ 0 →
          squarefreeKernel (targetProduct (starts x y z) M α) ∈ coefficients x L H t ∧
          0 < squarefreeKernel (targetProduct (starts x y z) M α) ∧
          squarefreeKernel (targetProduct (starts x y z) M α) ≤ N ^ (2 * (t - 1)) ∧
          IsSquare (((squarefreeKernel (targetProduct (starts x y z) M α) : ℕ) : ℤ) *
            targetProduct (starts x y z) M α) := by
  obtain ⟨NC, _hNC, hc⟩ := SourceSupportedCoefficientCount.uniform_count s (sourceBound s t) D C ε hD hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  refine ⟨max 3 (max NC NG), by omega, ?_⟩
  intro N hN L H hband hHlo hHhi x hx
  have hgeom := hg N (by omega) L hband
  have hLN : L ≤ N := by have h := hgeom.2.2.2.1; omega
  refine ⟨hc N (by omega) L H hband hHhi x hx, ?_⟩
  intro y z hy hz M hM α hα
  let X := starts x y z
  have hdyadic : ∀ i, X i ∈ dyadicBlock N := by
    intro i
    rcases i with i | j
    · exact hx i
    · by_cases hj : j = 0
      · simpa only [X, starts, hj, ite_true] using hy
      · simpa only [X, starts, hj, ite_false] using hz
  have hX : ∀ i, 2 ≤ X i := by
    intro i
    have h := (mem_Ico.mp (hdyadic i)).1
    omega
  have hmem : squarefreeKernel (targetProduct X M α) ∈ coefficients x L H t :=
    TwoTargetIntrinsicClassCoefficients.kernel_in_pool X M hX hHlo ht hM α hα
  have hpositive : 0 < squarefreeKernel (targetProduct X M α) := by
    apply prod_pos
    intro p hp
    exact (LargeOddKernel.prime_of_mem_oddPrimeSupport hp).pos
  have hheight : ∀ v ∈ LabelClassPartition.part (label X M) α, WindowPrimeIncidence.value X L v ≤ N ^ 2 := by
    intro v _hv
    have h := (OriginalWindowValueBounds.values_geometry N L (X v.1) (by omega)
      (mem_Ico.mp (hdyadic v.1)) hLN (startCompleteVertexLabel (X v.1) L v.2)
      (NormalizedWindowSets.mem_values.mpr ⟨v.2, rfl⟩)).1.2
    have hv : WindowPrimeIncidence.value X L v ≤ 3 * N := by exact_mod_cast h
    exact hv.trans (by nlinarith only [show 3 ≤ N by omega])
  have hbound := kernel_height X M hX (by omega) α (DisjointRecoverySubspace.coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code X L)) M (s + 1) t (by omega) hM α hα) hheight
  have hn : 0 < targetProduct X M α := prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos X hX v
  obtain ⟨r, hr⟩ := RelativeSquarefreeParts.kernel_mul_isSquare hn.ne'
  exact ⟨hmem, hpositive, hbound, (r : ℤ), by exact_mod_cast hr⟩

end PaperP1.TwoTargetIntrinsicEnumeration
