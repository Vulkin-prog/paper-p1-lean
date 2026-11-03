module

public import PaperP1.Arithmetic.OneTargetPhysicalRegularization
public import PaperP1.Asymptotics.TwoTargetPureClassData

/-! # Two actual labels of one free target give unconditional disjoint square equations from a common source-only list -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OneTargetClassSystem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.TwoTargetWindowSections PaperP1.TwoTargetPrimeClassSupports PaperP1.TwoTargetClassSourceCover
  PaperP1.SmallPrimeBudget PaperP1.DisjointRecoverySubspace PaperP1.TwoTargetLabelSelection

local instance oneTargetSystemPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance dualDecidableEq {s L : ℕ} (X : Fin s ⊕ Fin 2 → ℕ)
    (P : Submodule F₂ (code X L)) : DecidableEq (Module.Dual F₂ P) := Classical.decEq _

theorem of_two_labels {s y z L t : ℕ} (x : Fin s → ℕ) (hx : ∀ i, 2 ≤ x i) (hy : 2 ≤ y) (hz : 2 ≤ z)
    (P : Submodule F₂ (code (starts x y z) L)) (ht : 2 ≤ t)
    (hno : NoDisjointRecovery (CoordinateForms.coordinateFamily (code (starts x y z) L)) P (s + 1) t)
    (hzero : (projection (starts x y z) L (Sum.inr 1)).comp P.subtype = 0)
    (hmany : 2 ≤ (targetLabels (starts x y z) P 0).card) :
    CoefficientUnivariateCount.HasSystem L (t - 1) (TwoTargetCoefficientEnumeration.coefficients x L (L + 1) t) y := by
  have hX : ∀ i, 2 ≤ starts x y z i := by
    intro i
    rcases i with i | j
    · exact hx i
    · by_cases hj : j = 0
      · simpa only [starts, hj, ite_true] using hy
      · simpa only [starts, hj, ite_false] using hz
  obtain ⟨α, hinj, hα⟩ := exists_samples (targetLabels (starts x y z) P 0) 2 hmany
  have hdata (i : Fin 2) := (mem_target_labels (starts x y z) P 0 (α i)).mp (hα i)
  have hpure (i : Fin 2) :
      (TwoTargetClassOffsets.targetOffsets (LabelClassPartition.part (label (starts x y z) P) (α i)) 0).Nonempty ∧
      TwoTargetClassOffsets.targetOffsets (LabelClassPartition.part (label (starts x y z) P) (α i)) (0 : Fin 2).rev = ∅ :=
    ⟨(hdata i).2, OneTargetPhysicalRegularization.zero_projection_offsets _ P 1 hzero (α i) (hdata i).1⟩
  have hsize (i : Fin 2) := coordinate_multiplicity_le (CoordinateForms.coordinateFamily (code (starts x y z) L)) P
    (s + 1) t (by omega) hno (α i) (hdata i).1
  have hcoeff (i : Fin 2) : squarefreeKernel (targetProduct (starts x y z) P (α i)) ∈
      TwoTargetCoefficientEnumeration.coefficients x L (L + 1) t :=
    TwoTargetIntrinsicClassCoefficients.kernel_in_pool _ P hX le_rfl ht hno (α i) (hdata i).1
  have hsquare (i : Fin 2) : IsSquare
      (((squarefreeKernel (targetProduct (starts x y z) P (α i)) : ℕ) : ℤ) * targetProduct (starts x y z) P (α i)) := by
    have hpos : 0 < targetProduct (starts x y z) P (α i) :=
      prod_pos fun v _ ↦ TwoTargetPrimeClassSupports.value_pos _ hX v
    obtain ⟨r, hr⟩ := RelativeSquarefreeParts.kernel_mul_isSquare hpos.ne'
    exact ⟨(r : ℤ), by exact_mod_cast hr⟩
  exact TwoTargetPureClassData.exists_system x (by omega) (by omega) P _ 0 α hinj hpure hsize hcoeff hsquare

end PaperP1.OneTargetClassSystem
