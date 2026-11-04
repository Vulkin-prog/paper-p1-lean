module

public import PaperP1.Arithmetic.DeterminantCoordinateFlip
public import PaperP1.Arithmetic.DeterminantSourceBox

/-! # Exact positive-shift source boxes for either sign of the original equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSignedBoxes

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantCoordinateFlip
  PaperP1.TwoKernelDeterminantBoxes

def swappedBox {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) : Box N ρ C δ where
  c₁ := X.c₂
  c₂ := X.c₁
  D := X.E
  E := X.D
  U := X.V
  V := X.U
  c₁_ge_one := X.c₂_ge_one
  c₂_ge_one := X.c₁_ge_one
  D_ge_one := X.E_ge_one
  E_ge_one := X.D_ge_one
  U_ge_one := X.V_ge_one
  V_ge_one := X.U_ge_one
  first_lower := X.second_lower
  first_upper := X.second_upper
  second_lower := X.first_lower
  second_upper := X.first_upper
  first_log := by simpa only [mul_comm] using X.first_log
  second_log := by simpa only [mul_comm] using X.second_log

structure SignedPopulation {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (S : Finset Quad) : Prop where
  d_bounds : ∀ p ∈ S, X.D ≤ p.1.1 ∧ (p.1.1 : ℝ) ≤ 2 * X.D
  e_bounds : ∀ p ∈ S, X.E ≤ p.1.2 ∧ (p.1.2 : ℝ) ≤ 2 * X.E
  u_bounds : ∀ p ∈ S, X.U ≤ p.2.1 ∧ (p.2.1 : ℝ) ≤ 2 * X.U
  v_bounds : ∀ p ∈ S, X.V ≤ p.2.2 ∧ (p.2.2 : ℝ) ≤ 2 * X.V
  equation : ∀ p ∈ S, X.c₂ * (p.1.2 : ℝ) ^ 2 * p.2.2 = X.c₁ * (p.1.1 : ℝ) ^ 2 * p.2.1 + h

theorem swappedBox_involutive {N : ℕ} {ρ C δ : ℝ} : Function.Involutive (swappedBox (N := N) (ρ := ρ) (C := C) (δ := δ)) := by
  intro X
  rfl

theorem positive_population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (hh : 0 ≤ h)
    (S : Finset Quad) (hS : SignedPopulation X h S) : Population X h.natAbs S := by
  have habs : (h.natAbs : ℝ) = (h : ℝ) := by
    have hz : (h.natAbs : ℤ) = h := by rw [Int.natCast_natAbs, abs_of_nonneg hh]
    simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ ↦ (z : ℝ)) hz
  refine ⟨hS.d_bounds, hS.e_bounds, hS.u_bounds, hS.v_bounds, ?_⟩
  intro p hp
  simpa only [habs] using hS.equation p hp

theorem negative_population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ) (hh : h < 0)
    (S : Finset Quad) (hS : SignedPopulation X h S) :
    Population (swappedBox X) h.natAbs (S.image coordinateFlip) := by
  have habs : (h.natAbs : ℝ) = -(h : ℝ) := by
    have hz : (h.natAbs : ℤ) = -h := by rw [Int.natCast_natAbs, abs_of_neg hh]
    simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ ↦ (z : ℝ)) hz
  refine { d_bounds := ?_, e_bounds := ?_, u_bounds := ?_, v_bounds := ?_, equation := ?_ }
  all_goals intro p hp
  all_goals obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
  · exact hS.e_bounds q hq
  · exact hS.d_bounds q hq
  · exact hS.v_bounds q hq
  · exact hS.u_bounds q hq
  · have heq := hS.equation q hq
    change X.c₁ * (q.1.1 : ℝ) ^ 2 * q.2.1 = X.c₂ * (q.1.2 : ℝ) ^ 2 * q.2.2 + h.natAbs
    rw [habs]
    linarith only [heq]

theorem flipped_card (S : Finset Quad) : (S.image coordinateFlip).card = S.card :=
  card_image_of_injective S coordinateFlip_injective

theorem horizontalScale_swap {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (ζ : ℝ) :
    DeterminantHorizontalScale.horizontalScale N (swappedBox X).D (swappedBox X).E
      (swappedBox X).U (swappedBox X).V ζ =
        DeterminantHorizontalScale.horizontalScale N X.D X.E X.U X.V ζ := by
  simp only [DeterminantHorizontalScale.horizontalScale, DeterminantLogScale.logShape, swappedBox, mul_comm]

end PaperP1.DeterminantSignedBoxes
