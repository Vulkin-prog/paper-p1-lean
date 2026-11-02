module

public import PaperP1.Model.JointTupleSupport
public import PaperP1.Model.RunFamilyEnumeration
public import PaperP1.Asymptotics.FixedSourceMassStep
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Uniform actual joint rows after every nonempty bounded-size unordered seed -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualFamilyJointRows

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteFamilyEnumeration PaperP1.RunFamilyEnumeration

theorem append_support {s : ℕ} (x : Fin s → ℕ) (y : ℕ) :
    tupleSet (PrescribedTupleMass.append x y) = insert y (tupleSet x) := by
  ext z
  simp only [tupleSet, mem_image, mem_univ, true_and, mem_insert]
  change (∃ i : Fin (s + 1), Fin.snoc (α := fun _ : Fin (s + 1) ↦ ℕ) x y i = z) ↔ z = y ∨ ∃ i : Fin s, x i = z
  simp only [Fin.exists_fin_succ', Fin.snoc_last, Fin.snoc_castSucc]
  tauto

theorem uniform_row (r : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ I : Finset ℕ,
      I ⊆ dyadicBlock N → I.Nonempty → I.card ≤ r →
      (∑ y ∈ dyadicBlock N, infiniteJointMoment L (insert y I)) ≤
        (N : ℝ) ^ ε * infiniteJointMoment L I := by
  obtain ⟨NS, hs⟩ := FixedSourceMassStep.bounded_orders r C ε hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max 2 (max NS NG), by omega, ?_⟩
  intro N hN L hband I hI hne hcard
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  let x := canonical I.card I
  have hx : ∀ i, x i ∈ Ico N (2 * N) := by
    dsimp [x]
    rw [canonical_eq rfl]
    exact centres_mem (dyadicBlock N) I rfl hI
  have hsource := hs N (by omega) L hband I.card (by have h := card_pos.mpr hne; omega) hcard
    (fun _ ↦ Affine.startRhs L) {x} (by intro z hz; simpa only [mem_singleton.mp hz] using hx)
  rw [TupleExtensions.step_sum, sum_singleton, sum_singleton] at hsource
  simpa only [dyadicBlock, JointTupleSupport.prescribed_eq_support (hL := hL), append_support,
    x, canonical_values rfl] using hsource

end PaperP1.ActualFamilyJointRows
