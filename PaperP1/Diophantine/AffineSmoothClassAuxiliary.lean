module

public import PaperP1.Diophantine.AffineMonomialDeterminant
public import PaperP1.Arithmetic.DeterminantAuxiliaryPolynomial

/-! # An actual integer auxiliary equation for a full smooth affine residue class

The smallness condition uses the exact sum of affine monomial weights.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineSmoothClassAuxiliary

open Polynomial Finset DeterminantIntegerRows AffineMonomialDeterminant
open BiquadraticCoefficientPolynomials

theorem minor_vanishing (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (B : ℝ) (hB : 0 ≤ B) (S : Finset (ℤ × ℤ))
    (hx : ∀ z ∈ S, (p : ℤ) ∣ z.1 - a) (hy : ∀ z ∈ S, (p : ℤ) ∣ z.2 - b)
    (hz : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hxbox : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hybox : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2))
    (f : Exponent A J → S) :
    (Matrix.of (fun i j ↦ (entry (f i).val (j.1.val, j.2.val) : ℚ))).det = 0 := by
  have hv := vanishing p hp G a b hG hder A J B hB (fun i ↦ (f i).val)
    (fun i ↦ hx _ (f i).property) (fun i ↦ hy _ (f i).property)
    (fun i ↦ hz _ (f i).property) (fun i ↦ hxbox _ (f i).property)
    (fun i ↦ hybox _ (f i).property) hsmall
  have ht : (Matrix.of (fun i j ↦ entry (f i).val (j.1.val, j.2.val))).det = 0 := by
    change (matrix A J (fun i ↦ (f i).val)).transpose.det = 0
    rw [Matrix.det_transpose]
    exact hv
  have hc := congrArg (fun z : ℤ ↦ (z : ℚ)) ht
  rw [Int.cast_det, Int.cast_zero] at hc
  exact hc

theorem exists_coefficients (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (B : ℝ) (hB : 0 ≤ B) (S : Finset (ℤ × ℤ))
    (hx : ∀ z ∈ S, (p : ℤ) ∣ z.1 - a) (hy : ∀ z ∈ S, (p : ℤ) ∣ z.2 - b)
    (hz : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hxbox : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hybox : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2)) :
    ∃ w : Exponent A J → ℤ, w ≠ 0 ∧
      ∀ z ∈ S, ∑ i, entry z (i.1.val, i.2.val) * w i = 0 := by
  classical
  let nH := (univ : Finset S).sup (fun z ↦
    (univ : Finset (Exponent A J)).sup (fun i ↦ (entry z.val (i.1.val, i.2.val)).natAbs)) + 1
  have hb (z : S) (i : Exponent A J) : |entry z.val (i.1.val, i.2.val)| ≤ (nH : ℤ) := by
    have h₁ := Finset.le_sup (f := fun i : Exponent A J ↦ (entry z.val (i.1.val, i.2.val)).natAbs)
      (mem_univ i)
    have h₂ := Finset.le_sup (f := fun z : S ↦
      (univ : Finset (Exponent A J)).sup (fun i ↦ (entry z.val (i.1.val, i.2.val)).natAbs))
      (mem_univ z)
    have hn : (entry z.val (i.1.val, i.2.val)).natAbs ≤ nH := (h₁.trans h₂).trans (Nat.le_succ _)
    have hc : ((entry z.val (i.1.val, i.2.val)).natAbs : ℤ) ≤ (nH : ℤ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hc
  have hn : 0 < Fintype.card (Exponent A J) := by
    simp only [Exponent, Fintype.card_prod, Fintype.card_fin]
    positivity
  obtain ⟨w, hw, _hbound, hz⟩ := FiniteRowKernel.exists_integer_annihilator nH
    (by dsimp only [nH]; omega) hn (fun z : S ↦ fun i ↦ entry z.val (i.1.val, i.2.val)) hb
    (minor_vanishing p hp G a b hG hder A J B hB S hx hy hz hxbox hybox hsmall)
  exact ⟨w, hw, fun z hzS ↦ hz ⟨z, hzS⟩⟩

theorem exists_auxiliary (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (A J : ℕ) (B : ℝ) (hB : 0 ≤ B) (S : Finset (ℤ × ℤ))
    (hx : ∀ z ∈ S, (p : ℤ) ∣ z.1 - a) (hy : ∀ z ∈ S, (p : ℤ) ∣ z.2 - b)
    (hz : ∀ z ∈ S, G.evalEval z.1 z.2 = 0)
    (hxbox : ∀ z ∈ S, |(z.1 : ℝ)| ≤ B) (hybox : ∀ z ∈ S, |(z.2 : ℝ)| ≤ B)
    (hsmall : (((A + 1) * (J + 1)).factorial : ℝ) * B ^ weightSum A J <
      (p : ℝ) ^ (((A + 1) * (J + 1)) * (((A + 1) * (J + 1)) - 1) / 2)) :
    ∃ F : ℤ[X][X], F ≠ 0 ∧ BivariateDegrees.degreeX F ≤ A ∧ BivariateDegrees.degreeY F ≤ J ∧
      ∀ z ∈ S, F.evalEval z.1 z.2 = 0 := by
  obtain ⟨w, hw, hzero⟩ := exists_coefficients p hp G a b hG hder A J B hB S hx hy hz hxbox hybox hsmall
  refine ⟨rectangle A J w, DeterminantAuxiliaryPolynomial.rectangle_ne_zero A J w hw,
    rectangle_degreeX A J w, rectangle_degreeY A J w, ?_⟩
  intro z hzS
  have he := BivariateEvaluation.rectangle_evaluation z.1 z.2 A J w
  have heval : BivariateEvaluation.evaluate z.1 z.2 (rectangle A J w) =
      (rectangle A J w).evalEval z.1 z.2 := by
    simpa only [Int.cast_id] using
      BivariateEvaluation.integer_evaluation (R := ℤ) (rectangle A J w) z.1 z.2
  rw [heval] at he
  calc
    (rectangle A J w).evalEval z.1 z.2 = ∑ i, w i * z.1 ^ i.1.val * z.2 ^ i.2.val := he
    _ = ∑ i, entry z (i.1.val, i.2.val) * w i := by
      apply sum_congr rfl
      intro i _hi
      simp only [entry]
      ring
    _ = 0 := hzero z hzS

end PaperP1.AffineSmoothClassAuxiliary
