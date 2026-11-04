module

public import PaperP1.Algebra.RationalCurveCriticalPoints
public import PaperP1.Algebra.RationalBivariateIrreducibility
public import PaperP1.Algebra.BivariateCurveDegrees
public import PaperP1.Algebra.BivariateResultantHeight

/-! # A coefficient-uniform critical-point bound for actual rationalized factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RationalizedCriticalPointBound

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateCurveDegrees
  PaperP1.RationalBivariateIrreducibility

theorem outer_degree (G : ℤ[X][X]) : (rationalize G).natDegree = degreeY G := by
  unfold rationalize degreeY
  have hinj : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℚ)) :=
    Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  exact Polynomial.natDegree_map_eq_of_injective hinj G

theorem resultant_identity (G : ℤ[X][X]) :
    (rationalize G).resultant (rationalize G).derivative =
      (G.resultant G.derivative).map (Int.castRingHom ℚ) := by
  unfold rationalize
  rw [Polynomial.derivative_map]
  rw [Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective),
    Polynomial.natDegree_map_eq_of_injective
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective)]
  exact Polynomial.resultant_map_map G G.derivative G.natDegree G.derivative.natDegree
    (Polynomial.mapRingHom (Int.castRingHom ℚ))

theorem resultant_degree_bound (G : ℤ[X][X]) :
    ((rationalize G).resultant (rationalize G).derivative).natDegree ≤
      2 * degreeX G * degreeY G := by
  rw [resultant_identity]
  have hd : G.derivative.natDegree ≤ G.natDegree :=
    (Polynomial.natDegree_derivative_le G).trans (Nat.sub_le _ _)
  have hsum : G.natDegree + G.derivative.natDegree ≤ 2 * degreeY G := by
    change G.natDegree + G.derivative.natDegree ≤ 2 * G.natDegree
    omega
  calc
    _ ≤ (G.resultant G.derivative).natDegree := Polynomial.natDegree_map_le
    _ ≤ (G.natDegree + G.derivative.natDegree) * degreeX G :=
      PaperP1.BivariateResultantHeight.resultant_degree G G.derivative
        G.natDegree G.derivative.natDegree (degreeX G) le_rfl (degreeX_derivative_le G)
    _ ≤ (2 * degreeY G) * degreeX G := Nat.mul_le_mul_right _ hsum
    _ = _ := by ring

theorem critical_points_card (G : ℤ[X][X]) (hG : Irreducible (rationalize G))
    (hy : 0 < degreeY G) (S : Finset (ℚ × ℚ))
    (hS : ∀ p ∈ S, (rationalize G).evalEval p.1 p.2 = 0 ∧
      (rationalize G).derivative.evalEval p.1 p.2 = 0) :
    S.card ≤ 2 * degreeX G * degreeY G ^ 2 := by
  have hdeg : 0 < (rationalize G).natDegree := (outer_degree G).symm ▸ hy
  have hc := PaperP1.RationalCurveCriticalPoints.critical_points_card (F := ℚ)
    (rationalize G) hG hdeg S hS
  calc
    _ ≤ ((rationalize G).resultant (rationalize G).derivative).natDegree *
        (rationalize G).natDegree := hc
    _ ≤ (2 * degreeX G * degreeY G) * degreeY G :=
      Nat.mul_le_mul (resultant_degree_bound G) (outer_degree G).le
    _ = _ := by ring

end PaperP1.RationalizedCriticalPointBound
