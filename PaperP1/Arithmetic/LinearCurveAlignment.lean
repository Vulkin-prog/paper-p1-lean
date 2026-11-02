module

public import PaperP1.Algebra.BivariateLineGeometry
public import PaperP1.Arithmetic.BoundedPointAlignment
public import PaperP1.Arithmetic.CurveFromCompleteRelations

/-! # The actual degree-one common-curve case forces a source alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LinearCurveAlignment

open Finset Polynomial PaperP1.Arithmetic PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree
  PaperP1.BivariateLineGeometry PaperP1.CurveIntegerFibres PaperP1.ShortBasisActualSpace
  PaperP1.CompleteRelationWordEmbedding

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : CommRing ℤ[X][X] := inferInstance

theorem bounded_grid_alignment (P : ℤ[X][X]) (hD : totalDegree P = 1) (B : ℕ) (x y : ℤ)
    (hx : (B : ℤ) < x) (hy : (B : ℤ) < y) (hpoint : P.evalEval x y = 0)
    (hgrid : 2 ≤ (integerGrid P B).card) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a.Coprime b ∧ a ≤ 2 * B ∧ b ≤ 2 * B ∧
      |(b : ℤ) * x - (a : ℤ) * y| ≤ ((a + b : ℕ) : ℤ) * B := by
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp (by omega : 1 < (integerGrid P B).card)
  obtain ⟨hp₁, hp₂, hpP⟩ := (mem_integerGrid P B p).mp hp
  obtain ⟨hq₁, hq₂, hqP⟩ := (mem_integerGrid P B q).mp hq
  let p' : ℤ × ℤ := (-p.1, -p.2)
  let q' : ℤ × ℤ := (-q.1, -q.2)
  have hp' : |p'.1| ≤ (B : ℤ) ∧ |p'.2| ≤ (B : ℤ) := by
    simpa only [p', abs_neg] using And.intro hp₁ hp₂
  have hq' : |q'.1| ≤ (B : ℤ) ∧ |q'.2| ≤ (B : ℤ) := by
    simpa only [q', abs_neg] using And.intro hq₁ hq₂
  have hne : p' ≠ q' := by
    intro h
    apply hpq
    exact Prod.ext (neg_injective (congrArg Prod.fst h)) (neg_injective (congrArg Prod.snd h))
  have hcross := points_cross P hD p' q' (x, y) hpP hqP hpoint
  exact BoundedPointAlignment.alignment_of_cross B x y p' q' hx hy hp' hq' hne hcross

theorem actual_linear_case (x y L : ℕ) (hL : 1 ≤ L)
    (cert : ShortBasisActualSpace.Certificate x y L)
    (curve : CommonCurveTheorem.Certificate (wordSpace x y L cert))
    (ht : 9 ≤ Module.finrank F₂ cert.space) (hD : totalDegree curve.polynomial = 1)
    (hx : L + 1 < x) (hy : L + 1 < y)
    (hpoint : curve.polynomial.evalEval (x : ℤ) (y : ℤ) = 0) :
    CompressedTargetAlignment.Aligned 1 x y L := by
  have hgrid := CurveFromCompleteRelations.actual_grid_bound x y L cert curve
  have hmax : 1 ≤ max (degreeX curve.polynomial) (degreeY curve.polynomial) :=
    (show 1 ≤ degreeX curve.polynomial by have h := curve.degreeX_pos; omega).trans (le_max_left _ _)
  have hretained : 2 ≤ Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2 := by
    rw [hD]
    omega
  have hmul := Nat.mul_le_mul_right
    (Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2) hmax
  have hmul' : Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2 ≤
      max (degreeX curve.polynomial) (degreeY curve.polynomial) *
        (Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2) := by
    simpa only [one_mul] using hmul
  have htwo : 2 ≤ (integerGrid curve.polynomial (L + 1)).card :=
    hretained.trans (hmul'.trans hgrid)
  apply BoundedPointAlignment.source_alignment hL
  exact bounded_grid_alignment curve.polynomial hD (L + 1) (x : ℤ) (y : ℤ)
    (by exact_mod_cast hx) (by exact_mod_cast hy) hpoint htwo

theorem nonaligned_degree_ne_one (x y L : ℕ) (hL : 1 ≤ L)
    (cert : ShortBasisActualSpace.Certificate x y L)
    (curve : CommonCurveTheorem.Certificate (wordSpace x y L cert))
    (ht : 9 ≤ Module.finrank F₂ cert.space) (hx : L + 1 < x) (hy : L + 1 < y)
    (hpoint : curve.polynomial.evalEval (x : ℤ) (y : ℤ) = 0)
    (hnon : ¬ CompressedTargetAlignment.Aligned 1 x y L) : totalDegree curve.polynomial ≠ 1 :=
  fun hD ↦ hnon (actual_linear_case x y L hL cert curve ht hD hx hy hpoint)

end PaperP1.LinearCurveAlignment
