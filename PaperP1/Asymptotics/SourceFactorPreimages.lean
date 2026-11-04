module

public import PaperP1.Diophantine.ZeroPartialDegreeFactor
public import PaperP1.Diophantine.ActualIntegerSourceEquation

/-! # Pull actual factor populations back to subsets of the original source points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceFactorPreimages

open Finset Polynomial PaperP1.TwoKernelDeterminantBoxes PaperP1.ActualProjectivePairs
open PaperP1.BiformPointCoordinates PaperP1.FourProjectiveCharts PaperP1.IntegerPairFactorCover
open PaperP1.IntegerFactorProjectiveCurve PaperP1.BivariateDegrees PaperP1.ZeroPartialDegreeFactor
open PaperP1.BinaryLinearSubstitution PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes

def chartCoordinates (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) (p : Quad) :
    (Fin 2 → ℤ) × (Fin 2 → ℤ) := move (matrix c.1) (matrix c.2) (coordinates B D p)

def sourcePart (G : ℤ[X][X]) (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) (Q : Finset Quad) :
    Finset Quad := Q.filter (fun p ↦ MvPolynomial.eval₂ (MvPolynomial.eval (chartCoordinates B D c p).2)
      (chartCoordinates B D c p).1 (projective G) = 0)

def pullSecondForm (G : ℤ[X][X]) (B : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool) :
    MvPolynomial (Fin 2) ℤ := substitute (matrix c * B) (secondForm G)

theorem sourcePart_subset (G : ℤ[X][X]) (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) (Q : Finset Quad) :
    sourcePart G B D c Q ⊆ Q := filter_subset _ _

theorem factor_population_card_le_sourcePart (G : ℤ[X][X]) (B D : Matrix (Fin 2) (Fin 2) ℤ)
    (c : Bool × Bool) (Q : Finset Quad)
    (hden : ∀ q ∈ population c (Q.image (coordinates B D)), q.1 1 ≠ 0 ∧ q.2 1 ≠ 0) :
    (zeros G (population c (Q.image (coordinates B D)))).card ≤ (sourcePart G B D c Q).card := by
  have hsub : zeros G (population c (Q.image (coordinates B D))) ⊆
      (sourcePart G B D c Q).image (chartCoordinates B D c) := by
    intro q hq
    have hpop := (mem_filter.mp hq).1
    have hz := (IntegerPairFactorCharts.projective_zero_iff G q.1 q.2
      (hden q hpop).1 (hden q hpop).2).mpr (mem_filter.mp hq).2
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hpop
    obtain ⟨p, hp, rfl⟩ := mem_image.mp (mem_filter.mp hr).1
    exact mem_image.mpr ⟨p, mem_filter.mpr ⟨hp, hz⟩, rfl⟩
  exact (card_le_card hsub).trans (card_image_le)

theorem sourcePart_population {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} {h : ℤ}
    {Q : Finset Quad} (hQ : SignedPopulation X h Q) (G : ℤ[X][X])
    (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) : SignedPopulation X h (sourcePart G B D c Q) := by
  exact ⟨fun p hp ↦ hQ.d_bounds p (sourcePart_subset G B D c Q hp),
    fun p hp ↦ hQ.e_bounds p (sourcePart_subset G B D c Q hp),
    fun p hp ↦ hQ.u_bounds p (sourcePart_subset G B D c Q hp),
    fun p hp ↦ hQ.v_bounds p (sourcePart_subset G B D c Q hp),
    fun p hp ↦ hQ.equation p (sourcePart_subset G B D c Q hp)⟩

theorem pullSecondForm_homogeneous (G : ℤ[X][X]) (B : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool) :
    (pullSecondForm G B c).IsHomogeneous (degreeY G) :=
  substitute_homogeneous _ _ _ (secondForm_homogeneous G)

theorem pullSecondForm_nonzero (G : ℤ[X][X]) (hG : G ≠ 0) (hdegree : degreeX G = 0)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hBA : B * A = 1) (c : Bool) :
    pullSecondForm G B c ≠ 0 := by
  apply substitute_nonzero (matrix c * B) (A * matrix c) _ _ _ (secondForm_nonzero G hG hdegree)
  · calc
      _ = matrix c * (B * A) * matrix c := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.mul_one, matrix_squared]
  · calc
      _ = A * (matrix c * matrix c) * B := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [matrix_squared, Matrix.mul_one, hAB]

theorem sourcePart_second_form_zero (G : ℤ[X][X]) (hdegree : degreeX G = 0)
    (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) (Q : Finset Quad) :
    ∀ p ∈ sourcePart G B D c Q, MvPolynomial.eval (integerPoint p).2 (pullSecondForm G D c.2) = 0 := by
  intro p hp
  have hz := (mem_filter.mp hp).2
  rw [evaluation_first_degree_zero G hdegree] at hz
  unfold pullSecondForm
  rw [evaluation]
  simpa only [chartCoordinates, coordinates, move, Matrix.mulVec_mulVec] using hz

theorem sourcePart_first_form_zero (G : ℤ[X][X]) (hdegree : degreeY G = 0)
    (B D : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) (Q : Finset Quad) :
    ∀ p ∈ sourcePart G B D c Q,
      MvPolynomial.eval (integerPoint p).1 (pullSecondForm (Bivariate.swap G) B c.1) = 0 := by
  intro p hp
  have hz := (mem_filter.mp hp).2
  have hs := (BivariateProjectiveSwap.evaluation_swap G
    (chartCoordinates B D c p).1 (chartCoordinates B D c p).2).trans hz
  rw [evaluation_first_degree_zero (Bivariate.swap G)
    (by simpa only [BivariateProjectiveSwap.degreeX_swap] using hdegree)] at hs
  unfold pullSecondForm
  rw [evaluation]
  simpa only [chartCoordinates, coordinates, move, Matrix.mulVec_mulVec] using hs

end PaperP1.SourceFactorPreimages
