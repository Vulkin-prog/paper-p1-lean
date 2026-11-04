module

public import PaperP1.Arithmetic.DeterminantSignedBoxes

/-! # Exact positive orientation preserves source cardinalities, determinant scales and both costs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantPositiveOrientation

open Finset PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.DeterminantCoordinateFlip PaperP1.TwoKernelDeterminantBoxes
open PaperP1.DeterminantHorizontalScale PaperP1.DeterminantLogScale

def orientedBox {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) : Box N ρ C δ :=
  if h < 0 then swappedBox X else X

def orientedPopulation (h : ℤ) (S : Finset Quad) : Finset Quad :=
  if h < 0 then S.image coordinateFlip else S

theorem population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ)
    (S : Finset Quad) (hS : SignedPopulation X h S) :
    Population (orientedBox h X) h.natAbs (orientedPopulation h S) := by
  by_cases hn : h < 0
  · simpa only [orientedBox, orientedPopulation, ite_eq_left hn] using negative_population X h hn S hS
  · simpa only [orientedBox, orientedPopulation, ite_eq_right hn] using positive_population X h (by omega) S hS

theorem signed_population {N : ℕ} {ρ C δ : ℝ} (X : Box N ρ C δ) (h : ℤ)
    (S : Finset Quad) (hS : SignedPopulation X h S) :
    SignedPopulation (orientedBox h X) (h.natAbs : ℤ) (orientedPopulation h S) := by
  have hp := population X h S hS
  refine ⟨hp.d_bounds, hp.e_bounds, hp.u_bounds, hp.v_bounds, ?_⟩
  intro p hmem
  simpa only [Int.cast_natCast] using hp.equation p hmem

theorem card_eq (h : ℤ) (S : Finset Quad) : (orientedPopulation h S).card = S.card := by
  by_cases hn : h < 0
  · simpa only [orientedPopulation, ite_eq_left hn] using flipped_card S
  · simp only [orientedPopulation, ite_eq_right hn]

theorem scale_eq {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) (ζ : ℝ) :
    horizontalScale N (orientedBox h X).D (orientedBox h X).E (orientedBox h X).U (orientedBox h X).V ζ =
      horizontalScale N X.D X.E X.U X.V ζ := by
  by_cases hn : h < 0
  · simpa only [orientedBox, ite_eq_left hn] using horizontalScale_swap X ζ
  · simp only [orientedBox, ite_eq_right hn]

theorem shape_eq {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) :
    logShape N (orientedBox h X).D (orientedBox h X).E (orientedBox h X).U (orientedBox h X).V =
      logShape N X.D X.E X.U X.V := by
  by_cases hn : h < 0 <;> simp [orientedBox, hn, swappedBox, logShape, mul_comm]

theorem horizontal_cost_eq {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) (S : ℝ) :
    Real.sqrt ((orientedBox h X).D * (orientedBox h X).E * S) + (orientedBox h X).D + (orientedBox h X).E =
      Real.sqrt (X.D * X.E * S) + X.D + X.E := by
  by_cases hn : h < 0 <;> simp [orientedBox, hn, swappedBox, mul_comm, add_comm, add_left_comm]

theorem vertical_cost_eq {N : ℕ} {ρ C δ : ℝ} (h : ℤ) (X : Box N ρ C δ) (S : ℝ) :
    Real.sqrt ((orientedBox h X).U * (orientedBox h X).V * S) + (orientedBox h X).U + (orientedBox h X).V =
      Real.sqrt (X.U * X.V * S) + X.U + X.V := by
  by_cases hn : h < 0 <;> simp [orientedBox, hn, swappedBox, mul_comm, add_comm, add_left_comm]

end PaperP1.DeterminantPositiveOrientation
