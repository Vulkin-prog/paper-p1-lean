module

public import PaperP1.Arithmetic.WindowPrimeIncidence
public import PaperP1.Arithmetic.DenseTargetRegularization

/-! # Every active large target-prime row has an actual bounded source support -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCircuitSupports

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations
  PaperP1.WindowPrimeIncidence PaperP1.PhysicalLabelSupportCount PaperP1.DisjointRecoveryTheorem

local instance primeCircuitSupportTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance primeCircuitSupportDecEq (W : Type*) : DecidableEq W := Classical.decEq _

abbrev label {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) (M : Submodule F₂ (code X L))
    (v : Option (Fin s) × Fin (L + 1)) : Module.Dual F₂ M :=
  (CoordinateForms.coordinateFamily (code X L) v).comp M.subtype

abbrev allLabels {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) (M : Submodule F₂ (code X L)) :=
  RecoveryLabelSupports.labels (CoordinateForms.coordinateFamily (code X L)) M

abbrev pool {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) (M : Submodule F₂ (code X L))
    (α : Module.Dual F₂ M) := supportPool (label X L M) (allLabels X L M) s α

def throughPool {s : ℕ} (X : Option (Fin s) → ℕ) (L : ℕ) (M : Submodule F₂ (code X L))
    (v : Option (Fin s) × Fin (L + 1)) := (pool X L M (label X L M v)).image (insert v)

theorem old_support {s L p : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (hX : ∀ i, 1 ≤ X i) (hp : L + 1 < p) (v : Option (Fin s) × Fin (L + 1))
    (hvtarget : v.1 = none) (hv : v ∈ occurrences X L p) (hactive : label X L M v ≠ 0) :
    ∃ D ⊆ (occurrences X L p).erase v,
      D ∈ pool X L M (label X L M v) ∧ D.Nonempty ∧ D.card ≤ s ∧
      Set.InjOn (label X L M) (D : Set (Option (Fin s) × Fin (L + 1))) ∧
      (∑ w ∈ D, label X L M w) = label X L M v ∧ ∀ w ∈ D, w.1 ≠ none := by
  have hcard : ((occurrences X L p).erase v).card ≤ s := by
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_sub_cancel_right] using
      others_card hX hp hv
  have hlabels : ∀ w ∈ (occurrences X L p).erase v,
      label X L M w ≠ 0 → label X L M w ∈ allLabels X L M := by
    intro w _ hw
    exact (RecoveryLabelSupports.mem_labels _ M _).mpr ⟨hw, w, rfl⟩
  obtain ⟨D, hDsub, hDpool, hDne, hDcard, hDinj, hDsum⟩ :=
    RegularizedSupportPools.support_pool_contains (label X L M) (allLabels X L M) s
      ((occurrences X L p).erase v) hlabels hcard (label X L M v) hactive (others_label_sum M hv)
  refine ⟨D, hDsub, hDpool, hDne, hDcard, hDinj, hDsum, ?_⟩
  intro w hw
  have hblock := other_block hX hp hv (hDsub hw)
  rwa [hvtarget] at hblock

theorem inserted_support {s L p : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (v : Option (Fin s) × Fin (L + 1)) (hv : v ∈ occurrences X L p)
    (D : Finset (Option (Fin s) × Fin (L + 1))) (hD : D ⊆ (occurrences X L p).erase v)
    (hDne : D.Nonempty) (hsum : (∑ w ∈ D, label X L M w) = label X L M v) :
    (insert v D).card = D.card + 1 ∧ 2 ≤ (insert v D).card ∧
      (∀ w ∈ insert v D, p ∣ value X L w) ∧ (∑ w ∈ insert v D, label X L M w) = 0 := by
  have hvD : v ∉ D := fun h ↦ (mem_erase.mp (hD h)).1 rfl
  refine ⟨card_insert_of_notMem hvD, ?_, ?_, ?_⟩
  · rw [card_insert_of_notMem hvD]
    have h := hDne.card_pos
    omega
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact dvd_of_mem hv
    · exact dvd_of_mem (mem_erase.mp (hD hw)).2
  · rw [sum_insert hvD, hsum]
    exact PaperP1.PairFourierIntersection.self_add _

theorem throughPool_card {s L : ℕ} (X : Option (Fin s) → ℕ) (M : Submodule F₂ (code X L))
    (t : ℕ) (ht : 2 ≤ t)
    (hM : RecoveryConclusion (CoordinateForms.coordinateFamily (code X L)) M s t (t - 1))
    (v : Option (Fin s) × Fin (L + 1)) (hactive : label X L M v ≠ 0) :
    (throughPool X L M v).card ≤ supportBound s t (t - 1) := by
  have hno := RecoveryLabelSupports.noDisjointSums_of_recovery_exclusion
    (CoordinateForms.coordinateFamily (code X L)) M s t (by omega) hM.2.1
  apply card_image_le.trans
  apply supportPool_card _ _ s t (t - 1) hno
  · intro a ha
    exact hM.2.2.1 a ((RecoveryLabelSupports.mem_labels _ M a).mp ha).1
  · exact hactive

end PaperP1.PrimeCircuitSupports
