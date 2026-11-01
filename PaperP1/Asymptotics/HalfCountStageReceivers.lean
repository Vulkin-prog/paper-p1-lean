module

public import PaperP1.Asymptotics.HalfCountStages
public import PaperP1.Asymptotics.AnchorRelationCertificates
public import PaperP1.Arithmetic.HalfCountCertificateLists

/-! # Actual saturated lists have a new or old certificate receiver -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountStageReceivers

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountStages PaperP1.AnchorCertificateGraph PaperP1.BoundedIntegerMotifs

theorem witness_receiver {r s : ℕ} (G : Finset ℕ) (N X W t : ℕ) (Y : ℝ)
    (old : Fin s → ℕ) (hold : ∀ k, old k ∈ G) (n : Fin (r + 1) → ℕ)
    (hn : n ∈ lists G W old) (A : Fin (r + 1) → Finset ℤ) (hA : Witness W old n A)
    (i : Fin (r + 1)) (hlarge : t ≤ largeCount N Y (n i) (A i))
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin r) (κ := Fin s) G X W t Y N) :
    (∃ j : Fin r, n (i.succAbove j) ∈ outgoing G X W t Y (n i)) ∨
      ∃ k : Fin s, old k ∈ outgoing G X W t Y (n i) := by
  have hnG := ((mem_lists G W old n).mp hn).1
  have hsplit := Fin.add_sum_removeNth i (fun j ↦ vector (n j) (A j))
  change vector (n i) (A i) + (∑ j : Fin r, vector (i.removeNth n j) (i.removeNth A j)) =
    ∑ j, vector (n j) (A j) at hsplit
  have hrelation : vector (n i) (A i) +
      (∑ j : Fin r, vector (i.removeNth n j) (i.removeNth A j)) ∈
      PaperP1.OldSpaceProjection.oldSpace (PaperP1.OldBlockSelections.values old (fun _ ↦ offsets W)) := by
    change vector (n i) (A i) +
      (∑ j : Fin r, vector (i.removeNth n j) (i.removeNth A j)) ∈
      PaperP1.OldSpaceProjection.oldSpace (oldValues W old)
    rw [hsplit]
    exact hA.2
  obtain ⟨j, hj⟩ := hcontrol (n i) (hnG i) (i.removeNth n) old
    (fun j ↦ hnG (i.succAbove j)) hold (A i) (i.removeNth A) (fun _ ↦ offsets W)
    ((subset_offsets W (A i)).mp (hA.1 i).2.1)
    (fun j ↦ (subset_offsets W (A (i.succAbove j))).mp (hA.1 (i.succAbove j)).2.1)
    (fun _ u hu ↦ (subset_offsets W (offsets W)).mp Subset.rfl u hu) hlarge hrelation
  cases j with
  | inl j => exact Or.inl ⟨j, hj⟩
  | inr k => exact Or.inr ⟨k, hj⟩

theorem removed_receiver {r s : ℕ} (G : Finset ℕ) (N X W : ℕ) (old : Fin s → ℕ)
    (hold : ∀ k, old k ∈ G) (m t j : ℕ) (Y : ℕ → ℝ) (n : Fin (r + 1) → ℕ)
    (hn : n ∈ survivors G N W old m t Y j \ survivors G N W old m t Y (j + 1))
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin r) (κ := Fin s) G X W t (Y j) N) :
    ∃ i, m < (chosen W old n i).card ∧
      ((∃ k : Fin r, n (i.succAbove k) ∈ outgoing G X W t (Y j) (n i)) ∨
        ∃ k : Fin s, old k ∈ outgoing G X W t (Y j) (n i)) := by
  obtain ⟨i, hi, hlarge⟩ := removed_source G N W old m t j Y n hn
  have hnL := (survivor_data G N W old m t j Y n (mem_sdiff.mp hn).1).1
  exact ⟨i, hi, witness_receiver G N X W t (Y j) old hold n hnL
    (chosen W old n) (chosen_spec G W old n hnL) i hlarge hcontrol⟩

theorem survivor_has_coordinate {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t j : ℕ) (Y : ℕ → ℝ) (P : Finset ℕ)
    (hP : ∀ n ∈ survivors (r := r) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ P) :
    survivors (r := r) G N W old m t Y j ⊆ (lists G W old).filter fun n ↦ ∃ i, n i ∈ P := by
  classical
  intro n hn
  obtain ⟨hnL, hnshort, _⟩ := survivor_data G N W old m t j Y n hn
  obtain ⟨i, hi⟩ := long_index G W old n m hnL hnshort
  exact mem_filter.mpr ⟨hnL, i, hP n hn i hi⟩

theorem removed_cover {r s : ℕ} (G P : Finset ℕ) (N X W : ℕ) (old : Fin s → ℕ)
    (hold : ∀ k, old k ∈ G) (m t j : ℕ) (Y : ℕ → ℝ)
    (hP : ∀ n ∈ survivors (r := r + 1) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ P)
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin r) (κ := Fin s) G X W t (Y j) N) :
    survivors (r := r + 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1) ⊆
      PaperP1.HalfCountCertificateLists.newReceiverLists G P X W t (Y j) old ∪
        PaperP1.HalfCountCertificateLists.oldReceiverLists G X W t (Y j) old := by
  classical
  intro n hn
  have hnS := (mem_sdiff.mp hn).1
  have hnL := (survivor_data G N W old m t j Y n hnS).1
  obtain ⟨i, hi, hreceiver⟩ := removed_receiver G N X W old hold m t j Y n hn hcontrol
  rcases hreceiver with ⟨k, hk⟩ | ⟨k, hk⟩
  · apply mem_union_left
    exact mem_filter.mpr ⟨hnL, i, k,
      (PaperP1.CertificatePairs.mem_pairs P G X W t (Y j) _ _).mpr ⟨hP n hnS i hi, hk⟩⟩
  · apply mem_union_right
    exact mem_filter.mpr ⟨hnL, i, k,
      (PaperP1.CertificatePairs.outgoing_iff_incoming G X W t (Y j) _ _
        (((mem_lists G W old n).mp hnL).1 i) (hold k)).mp hk⟩

end PaperP1.HalfCountStageReceivers
