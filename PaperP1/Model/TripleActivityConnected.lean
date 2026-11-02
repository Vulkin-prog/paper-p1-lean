module

public import PaperP1.Affine.TripleFullSupportConnected
public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.ConnectedWindowFamilies
public import PaperP1.Model.CompatibleActivitySplit

/-! # Actual nonzero triple activities are connected; their positive part is exact -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TripleActivityConnected

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance tripleActivityConnectedDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem connected_of_coefficient_ne_zero (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.card = 3)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) (hc : infiniteCenteredCoefficient L I ≠ 0) :
    ConnectedWindowFamilies.Connected L I := by
  classical
  let M := I.sup fun x ↦ x + L
  have hcut : ∀ x : I, x.val + L ≤ M := fun x ↦ le_sup (f := fun x ↦ x + L) x.property
  have hcenter : infiniteFamilyCenteredMoment L (fun x : I ↦ x.val) ≠ 0 := by
    rwa [← infiniteCenteredCoefficient_eq_family_subtype]
  obtain ⟨s, hs⟩ := squareClass_full_relation_of_ne_zero M L (fun x : I ↦ x.val) hL hcut
    (fun x ↦ hp x.val x.property) hcenter
  apply TripleFullSupportConnected.connected _ _ s hs
  simpa only [Fintype.card_coe] using hI

theorem coefficient_zero_of_disconnected (L : ℕ) (hL : 0 < L) (I : Finset ℕ) (hI : I.card = 3)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) (hconn : ¬ConnectedWindowFamilies.Connected L I) :
    infiniteCenteredCoefficient L I = 0 := by
  by_contra hc
  exact hconn (connected_of_coefficient_ne_zero L hL I hI hp hc)

def positiveConnected (L : ℕ) (F : Finset (Finset ℕ)) : ℝ :=
  ∑ I ∈ F.filter (fun I ↦ ConnectedWindowFamilies.Connected L I ∧ 0 < infiniteJointMoment L I),
    infiniteCenteredCoefficient L I

theorem positive_eq_connected (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hsize : ∀ I ∈ F, I.card = 3) (hp : ∀ I ∈ F, ∀ x ∈ I, 0 < infiniteMarginal x L) :
    CompatibleActivitySplit.positive L F = positiveConnected L F := by
  unfold CompatibleActivitySplit.positive positiveConnected
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro I hI
  by_cases hconn : ConnectedWindowFamilies.Connected L I
  · simp only [hconn, true_and]
  · have hzero := coefficient_zero_of_disconnected L hL I (hsize I hI) (hp I hI) hconn
    simp only [hzero, hconn, false_and, ite_self]

theorem absolute_comparison (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hsize : ∀ I ∈ F, I.card = 3) (hp : ∀ I ∈ F, ∀ x ∈ I, 0 < infiniteMarginal x L) :
    CompatibleActivitySplit.absolute L F - positiveConnected L F = CompatibleActivitySplit.incompatibleAbsolute L F := by
  rw [← positive_eq_connected L hL F hsize hp]
  exact CompatibleActivitySplit.absolute_minus_positive L hL F

theorem signed_comparison (L : ℕ) (hL : 0 < L) (F : Finset (Finset ℕ))
    (hsize : ∀ I ∈ F, I.card = 3) (hp : ∀ I ∈ F, ∀ x ∈ I, 0 < infiniteMarginal x L) :
    |CompatibleActivitySplit.signed L F - positiveConnected L F| ≤ CompatibleActivitySplit.incompatibleAbsolute L F := by
  rw [← positive_eq_connected L hL F hsize hp]
  exact CompatibleActivitySplit.signed_error L F

end PaperP1.TripleActivityConnected
