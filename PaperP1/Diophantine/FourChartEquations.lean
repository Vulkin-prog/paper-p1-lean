module

public import PaperP1.Diophantine.FourProjectiveCharts
public import PaperP1.Asymptotics.BiformCoordinateHeight

/-! # Four nonzero bounded-height curve equations covering every primitive point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FourChartEquations

open Finset PaperP1.FourProjectiveCharts PaperP1.BiformPointCoordinates
open PaperP1.BiformLinearCoordinates PaperP1.BiformCoordinateEquation

variable {a b : ℕ}

def family (c : Bool × Bool) (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) :
    Fin (a + 1) → MvPolynomial (Fin 2) ℤ := transform (b := b) (matrix c.1) (matrix c.2) F

theorem family_homogeneous (c : Bool × Bool) (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) :
    ∀ i, (family (b := b) c F i).IsHomogeneous b := transform_homogeneous _ _ _

theorem curve_nonzero (c : Bool × Bool) (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (hF0 : F ≠ 0) : equation (b := b) (family (b := b) c F) ≠ 0 :=
  transformed_equation_nonzero _ _ _ _ (matrix_squared c.1) (matrix_squared c.1)
    (matrix_squared c.2) (matrix_squared c.2) F hF hF0

theorem population_zero (c : Bool × Bool) (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hS : ∀ p ∈ S, BidegreeOneElimination.original F p.1 p.2 = 0) :
    ∀ q ∈ population c S,
      MvPolynomial.eval₂ (MvPolynomial.eval q.2) q.1 (equation (b := b) (family (b := b) c F)) = 0 :=
  transported_population_zero _ _ _ _ (matrix_squared c.1) (matrix_squared c.2) F hF (part c S)
    (fun p hp ↦ hS p (mem_filter.mp hp).1)

theorem curve_height (c : Bool × Bool) (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (H : ℕ)
    (hH : ∀ i m, ((F i).coeff m).natAbs ≤ H) :
    ∀ m n, |((equation (b := b) (family (b := b) c F)).coeff m).coeff n| ≤
      (((b + 1) * ((a + 1) * H * 2 ^ a) * 2 ^ b : ℕ) : ℤ) := by
  simpa only [family, mul_one] using transformed_equation_height (matrix c.1) (matrix c.2) F hF H 1 1
    hH (matrix_height c.1) (matrix_height c.2)

theorem uniform_four_chart_reduction (Amax Bmax κ : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ a ≤ Amax, ∀ b ≤ Bmax,
      ∀ F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ,
      (∀ i, (F i).IsHomogeneous b) → F ≠ 0 →
      (∀ i m, ((F i).coeff m).natAbs ≤ N ^ κ) →
      ∀ S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
      (∀ p ∈ S, (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs) →
      (∀ p ∈ S, BidegreeOneElimination.original F p.1 p.2 = 0) →
      S.card = ∑ c : Bool × Bool, (population c S).card ∧
      ∀ c : Bool × Bool, equation (b := b) (family (b := b) c F) ≠ 0 ∧
        (equation (b := b) (family (b := b) c F)).IsHomogeneous a ∧
        (∀ i, (family (b := b) c F i).IsHomogeneous b) ∧
        (∀ m n, |((equation (b := b) (family (b := b) c F)).coeff m).coeff n| ≤ ((N ^ κ' : ℕ) : ℤ)) ∧
        ∀ q ∈ population c S, q.1 1 ≠ 0 ∧ q.2 1 ≠ 0 ∧
          (q.1 0).natAbs.Coprime (q.1 1).natAbs ∧ (q.2 0).natAbs.Coprime (q.2 1).natAbs ∧
          MvPolynomial.eval₂ (MvPolynomial.eval q.2) q.1 (equation (b := b) (family (b := b) c F)) = 0 := by
  obtain ⟨κ', N₀, hheight⟩ := BiformCoordinateHeight.uniform_transformed_height Amax Bmax κ 0 0
  refine ⟨κ', N₀, ?_⟩
  intro N hN a ha b hb F hF hF0 hH S hprimitive hzero
  refine ⟨finite_partition S, ?_⟩
  intro c
  refine ⟨curve_nonzero c F hF hF0, equation_homogeneous _, family_homogeneous c F, ?_, ?_⟩
  · exact hheight N hN a ha b hb (matrix c.1) (matrix c.2) F hF hH
      (by simpa only [pow_zero] using matrix_height c.1) (by simpa only [pow_zero] using matrix_height c.2)
  · intro q hq
    have hd := population_denominators c S (fun p hp ↦
      ⟨PaperP1.UnimodularBinaryCoordinates.primitive_nonzero _ (hprimitive p hp).1,
       PaperP1.UnimodularBinaryCoordinates.primitive_nonzero _ (hprimitive p hp).2⟩) q hq
    have hp := population_primitive c S hprimitive q hq
    exact ⟨hd.1, hd.2, hp.1, hp.2, population_zero c F hF S hzero q hq⟩

end PaperP1.FourChartEquations
