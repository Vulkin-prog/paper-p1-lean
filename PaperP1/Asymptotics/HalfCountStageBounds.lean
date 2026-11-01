module

public import PaperP1.Asymptotics.HalfCountStageReceivers
public import PaperP1.Asymptotics.HalfCountStageConfinement

/-! # Finite stage losses in terms of actual fewer-target list cardinalities

These finite inequalities do not assert the asymptotic half-count. Their
fewer-target cardinal bounds must be supplied by an actual induction.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountStageBounds

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountStages PaperP1.AnchorCertificateGraph PaperP1.HalfCountCertificateLists

theorem removed_bound {r s : ℕ} (G P : Finset ℕ) (N X W : ℕ) (old : Fin s → ℕ)
    (hold : ∀ k, old k ∈ G) (m t j : ℕ) (Y : ℕ → ℝ) (D B₁ B₂ : ℝ)
    (hPsub : P ⊆ G)
    (hP : ∀ n ∈ survivors (r := r + 2) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ P)
    (hdegree : ∀ x ∈ G, ((outgoing G X W t (Y j) x).card : ℝ) ≤ D ∧
      ((incoming G X W t (Y j) x).card : ℝ) ≤ D)
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin (r + 1)) (κ := Fin s) G X W t (Y j) N)
    (hB₁ : ∀ x ∈ G, ((lists (r := r + 1) G W (Fin.cons x old)).card : ℝ) ≤ B₁)
    (hB₂ : ∀ x ∈ G, ∀ y ∈ G,
      ((lists (r := r) G W (Fin.cons y (Fin.cons x old))).card : ℝ) ≤ B₂)
    (hB₁pos : 0 ≤ B₁) (hB₂pos : 0 ≤ B₂) :
    ((survivors (r := r + 2) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
      (((r + 2) * (r + 1) : ℕ) : ℝ) * ((P.card : ℝ) * D * B₂) +
        (((r + 2) * s : ℕ) : ℝ) * (D * B₁) := by
  classical
  have hcover := PaperP1.HalfCountStageReceivers.removed_cover G P N X W old hold m t j Y hP hcontrol
  have hc : ((survivors (r := r + 2) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
      ((newReceiverLists (r := r + 1) G P X W t (Y j) old).card : ℝ) +
        ((oldReceiverLists (r := r + 1) G X W t (Y j) old).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  exact hc.trans (add_le_add
    (new_receiver_bound G P X W t (Y j) D B₂ old hPsub (fun x hx ↦ (hdegree x (hPsub hx)).1) hB₂ hB₂pos)
    (old_receiver_bound G X W t (Y j) D B₁ old (fun k ↦ (hdegree (old k) (hold k)).2) hB₁ hB₁pos))

theorem removed_single_bound {s : ℕ} (G : Finset ℕ) (N X W : ℕ) (old : Fin s → ℕ)
    (hold : ∀ k, old k ∈ G) (m t j : ℕ) (Y : ℕ → ℝ) (D B : ℝ)
    (hdegree : ∀ x ∈ G, ((incoming G X W t (Y j) x).card : ℝ) ≤ D)
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin 0) (κ := Fin s) G X W t (Y j) N)
    (hB : ∀ x ∈ G, ((lists (r := 0) G W (Fin.cons x old)).card : ℝ) ≤ B)
    (hBpos : 0 ≤ B) :
    ((survivors (r := 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
      (s : ℝ) * (D * B) := by
  classical
  have hP : ∀ n ∈ survivors (r := 1) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ G := by
    intro n hn i _
    exact ((mem_lists G W old n).mp (survivor_data G N W old m t j Y n hn).1).1 i
  have hcover := PaperP1.HalfCountStageReceivers.removed_cover G G N X W old hold m t j Y hP hcontrol
  rw [no_new_receiver, empty_union] at hcover
  have hc : ((survivors (r := 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
      ((oldReceiverLists (r := 0) G X W t (Y j) old).card : ℝ) := by exact_mod_cast card_le_card hcover
  exact hc.trans (by
    simpa only [Nat.zero_add, Nat.one_mul] using
      old_receiver_bound G X W t (Y j) D B old (fun k ↦ hdegree (old k) (hold k)) hB hBpos)

theorem survivors_coordinate_bound {r s : ℕ} (G P : Finset ℕ) (N W : ℕ)
    (old : Fin s → ℕ) (m t j : ℕ) (Y : ℕ → ℝ) (B : ℝ)
    (hP : ∀ n ∈ survivors (r := r + 1) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ P)
    (hB : ∀ x ∈ P, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤ B) :
    ((survivors (r := r + 1) G N W old m t Y j).card : ℝ) ≤
      (r + 1 : ℝ) * ((P.card : ℝ) * B) := by
  classical
  have hcover := PaperP1.HalfCountStageReceivers.survivor_has_coordinate G N W old m t j Y P hP
  exact (show ((survivors (r := r + 1) G N W old m t Y j).card : ℝ) ≤
    (((lists (r := r + 1) G W old).filter fun n ↦ ∃ i, n i ∈ P).card : ℝ) by
      exact_mod_cast card_le_card hcover).trans
    (PaperP1.ProjectedWindowCounts.any_coordinate_bound G W old P B hB)

end PaperP1.HalfCountStageBounds
