module

public import PaperP1.Arithmetic.IntegralSourceCoefficients
public import PaperP1.Arithmetic.ActualProjectivePairs
public import PaperP1.Diophantine.SourceBihomogeneousEquation
public import PaperP1.Asymptotics.IntegerPairFactorCover
public import PaperP1.Diophantine.FourProjectiveCharts

/-! # The actual integer source equation holds on every transformed chart-factor population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualIntegerSourceEquation

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
open PaperP1.TwoKernelDeterminantBoxes PaperP1.IntegralSourceCoefficients PaperP1.ActualProjectivePairs
open PaperP1.SourceBihomogeneousEquation PaperP1.BiformLinearCoordinates PaperP1.FourProjectiveCharts

def coordinateFamily {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) : Fin 3 → MvPolynomial (Fin 2) ℤ :=
  transform (b := 1) A B (sourceForms (d.c₁ : ℤ) (d.c₂ : ℤ))

def chartFamily {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) : Fin 3 → MvPolynomial (Fin 2) ℤ :=
  transform (b := 1) (matrix c.1) (matrix c.2) (coordinateFamily d A B)

theorem source_value {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (h : ℤ) (S : Finset Quad) (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) :
    BidegreeOneElimination.original (sourceForms (d.c₁ : ℤ) (d.c₂ : ℤ)) (integerPoint p).1 (integerPoint p).2 = h := by
  have heqR : ((d.c₂ : ℤ) : ℝ) * (p.1.2 : ℝ) ^ 2 * p.2.2 =
      ((d.c₁ : ℤ) : ℝ) * (p.1.1 : ℝ) ^ 2 * p.2.1 + h := by
    simpa only [d.first_eq, d.second_eq, Int.cast_natCast] using hS.equation p hp
  have heq : (d.c₂ : ℤ) * (p.1.2 : ℤ) ^ 2 * p.2.2 =
      (d.c₁ : ℤ) * (p.1.1 : ℤ) ^ 2 * p.2.1 + h := by exact_mod_cast heqR
  rw [source_evaluation]
  change (d.c₂ : ℤ) * (p.1.2 : ℤ) ^ 2 * p.2.2 - (d.c₁ : ℤ) * (p.1.1 : ℤ) ^ 2 * p.2.1 = h
  linarith only [heq]

theorem coordinate_value {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B C D : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hCD : C * D = 1)
    (h : ℤ) (S : Finset Quad) (hS : SignedPopulation X h S) (p : Quad) (hp : p ∈ S) :
    BidegreeOneElimination.original (coordinateFamily d A C) (coordinates B D p).1 (coordinates B D p).2 = h := by
  have hv := inverse_equation_value A B C D hAB hCD (sourceForms (d.c₁ : ℤ) (d.c₂ : ℤ))
    (source_homogeneous (d.c₁ : ℤ) (d.c₂ : ℤ)) (integerPoint p)
  exact hv.trans (source_value d h S hS p hp)

theorem chart_homogeneous {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B : Matrix (Fin 2) (Fin 2) ℤ) (c : Bool × Bool) : ∀ i, (chartFamily d A B c i).IsHomogeneous 1 :=
  transform_homogeneous (matrix c.1) (matrix c.2) (coordinateFamily d A B)

theorem chart_population_value {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B C D : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hCD : C * D = 1)
    (h : ℤ) (S : Finset Quad) (hS : SignedPopulation X h S) (c : Bool × Bool) :
    ∀ q ∈ population c (S.image (coordinates B D)),
      BidegreeOneElimination.original (chartFamily d A C c) q.1 q.2 = h := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hq
  have hrP := (mem_filter.mp hr).1
  obtain ⟨p, hp, rfl⟩ := mem_image.mp hrP
  have hF : ∀ i, (coordinateFamily d A C i).IsHomogeneous 1 := transform_homogeneous A C _
  have hv := inverse_equation_value (matrix c.1) (matrix c.1) (matrix c.2) (matrix c.2)
    (matrix_squared c.1) (matrix_squared c.2) (coordinateFamily d A C) hF (coordinates B D p)
  exact hv.trans (coordinate_value d A B C D hAB hCD h S hS p hp)

theorem factor_population_value {N : ℕ} {ρ C δ : ℝ} {X : Box N ρ C δ} (d : IntegerCoefficients X)
    (A B C D : Matrix (Fin 2) (Fin 2) ℤ) (hAB : A * B = 1) (hCD : C * D = 1)
    (h : ℤ) (S : Finset Quad) (hS : SignedPopulation X h S) (c : Bool × Bool) (G : ℤ[X][X]) :
    ∀ q ∈ IntegerPairFactorCover.zeros G (population c (S.image (coordinates B D))),
      BidegreeOneElimination.original (chartFamily d A C c) q.1 q.2 = h := by
  intro q hq
  exact chart_population_value d A B C D hAB hCD h S hS c q (mem_filter.mp hq).1

end PaperP1.ActualIntegerSourceEquation
