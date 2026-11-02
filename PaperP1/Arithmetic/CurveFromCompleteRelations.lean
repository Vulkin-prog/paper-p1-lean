module

public import PaperP1.Arithmetic.CompleteRelationWordSquares
public import PaperP1.Arithmetic.IntegerGridTheorem

/-! # The actual common curve and grid bound of a complete-relation short basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveFromCompleteRelations

open Polynomial PaperP1.Arithmetic PaperP1.Affine PaperP1.BivariateDegrees
  PaperP1.BivariateTotalDegree PaperP1.BivariateHeight PaperP1.ShortBasisActualSpace
  PaperP1.CompleteRelationWordEmbedding PaperP1.CompleteRelationWordSquares
  PaperP1.CurveWordMap PaperP1.FormalWordPolynomials PaperP1.CurveIntegerFibres

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : CommRing ℤ[X][X] := inferInstance
local instance : AddCommGroup Words := inferInstance
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

theorem common_curve (x y L q : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (cert : ShortBasisActualSpace.Certificate x y L) (ht : 2 ≤ Module.finrank F₂ cert.space)
    (hq : 1 ≤ q) (hqB : q ≤ L + 1)
    (hsupport : ∀ i, (physicalCoefficients x y L (cert.basis i).val).support.card ≤ 2 * q)
    (N : ℝ) (hxN : N ≤ (x : ℝ)) (hyN : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : (((L + 1 : ℕ) : ℝ) + 1) ^ (1000000 * q ^ 2) < N) :
    ∃ curve : CommonCurveTheorem.Certificate (wordSpace x y L cert),
      curve.polynomial.evalEval (x : ℤ) (y : ℤ) = 0 ∧
      totalDegree curve.polynomial ≤ 48 * q ∧ height curve.polynomial ≤ (L + 1 + 1) ^ (2472 * q) := by
  classical
  let : Fintype cert.index := FiniteDimensional.fintypeBasisIndex (K := F₂) (V := cert.space) cert.basis
  let n := Fintype.card cert.index
  let e := Fintype.equivFin cert.index
  let b := (wordBasis x y L cert).reindex e
  let I : Fin n → Finset ℤ := fun i ↦ (b i).val.1.support
  let J : Fin n → Finset ℤ := fun i ↦ (b i).val.2.support
  have hdim : Module.finrank F₂ cert.space = n := Module.finrank_eq_card_basis cert.basis
  have hn : 2 ≤ n := by omega
  have htotal (i : Fin n) : (I i).card + (J i).card ≤ 2 * q := by
    change ((wordBasis x y L cert).reindex e i).val.1.support.card +
      ((wordBasis x y L cert).reindex e i).val.2.support.card ≤ 2 * q
    rw [Module.Basis.reindex_apply, wordBasis_support_card]
    exact hsupport _
  exact CommonCurveTheorem.integer_parameters hn (wordSpace x y L cert) b I J
    (fun i ↦ FormalWordEncoding.support_representation (b i).val) (L + 1) q hq hqB
    (fun i ↦ (wordSpace_even x y L cert (b i)).1)
    (fun i ↦ (wordSpace_even x y L cert (b i)).2)
    (fun i ↦ by have h := htotal i; omega) (fun i ↦ by have h := htotal i; omega)
    (fun i ↦ (wordSpace_offsets_bound x y L cert (b i)).1)
    (fun i ↦ (wordSpace_offsets_bound x y L cert (b i)).2)
    N (x : ℤ) (y : ℤ)
    (by simpa only [Int.cast_natCast] using hxN) (by simpa only [Int.cast_natCast] using hyN)
    (by simpa only [Int.cast_natCast] using hx₂) (by simpa only [Int.cast_natCast] using hy₂)
    hlarge (fun i ↦ wordSpace_square x y L hx hy cert (b i))

theorem actual_grid_bound (x y L : ℕ) (cert : ShortBasisActualSpace.Certificate x y L)
    (curve : CommonCurveTheorem.Certificate (wordSpace x y L cert)) :
    max (degreeX curve.polynomial) (degreeY curve.polynomial) *
      (Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2) ≤
        (integerGrid curve.polynomial (L + 1)).card := by
  let : Module.Finite F₂ (wordSpace x y L cert) := Module.Finite.equiv (wordEquiv x y L cert)
  obtain ⟨hfirst, hsecond⟩ := wordSpace_projections_injective x y L cert
  have h := IntegerGridTheorem.certificate_grid_bound (wordSpace x y L cert) curve (L + 1)
    hfirst hsecond
    (fun w u hu ↦ (mem_offsetBox (L + 1) u).mpr ((wordSpace_offsets_bound x y L cert w).1 u hu))
    (fun w v hv ↦ (mem_offsetBox (L + 1) v).mpr ((wordSpace_offsets_bound x y L cert w).2 v hv))
  simpa only [wordSpace_finrank] using h

theorem grid_rank_budget (x y L : ℕ) (cert : ShortBasisActualSpace.Certificate x y L)
    (curve : CommonCurveTheorem.Certificate (wordSpace x y L cert)) :
    (Module.finrank F₂ cert.space : ℝ) ≤ ((integerGrid curve.polynomial (L + 1)).card : ℝ) +
      1 + 6 * (totalDegree curve.polynomial : ℝ) ^ 2 := by
  have hg := actual_grid_bound x y L cert curve
  have hm : 1 ≤ max (degreeX curve.polynomial) (degreeY curve.polynomial) :=
    (show 1 ≤ degreeX curve.polynomial by have h := curve.degreeX_pos; omega).trans (le_max_left _ _)
  have hmul := Nat.mul_le_mul_right
    (Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2) hm
  have hmul' : Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2 ≤
      max (degreeX curve.polynomial) (degreeY curve.polynomial) *
        (Module.finrank F₂ cert.space - 1 - 6 * totalDegree curve.polynomial ^ 2) := by
    simpa only [one_mul] using hmul
  have hnat : Module.finrank F₂ cert.space ≤ (integerGrid curve.polynomial (L + 1)).card +
      1 + 6 * totalDegree curve.polynomial ^ 2 := by
    have h := hmul'.trans hg
    omega
  exact_mod_cast hnat

end PaperP1.CurveFromCompleteRelations
