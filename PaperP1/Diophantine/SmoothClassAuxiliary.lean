module

public import PaperP1.Diophantine.ProjectiveDeterminantVanishing
public import PaperP1.Diophantine.BidegreeOneFibreCount
public import PaperP1.Arithmetic.IntegerPairFactorCharts

/-! # A common integer auxiliary polynomial on an entire finite smooth residue class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothClassAuxiliary

open Polynomial Finset PaperP1.DeterminantIntegerRows PaperP1.BidegreeOneFibreCount
open PaperP1.BiquadraticCoefficientPolynomials PaperP1.BivariateDegrees

structure ClassPoint (p : ℕ) (G : ℤ[X][X]) (a b : ℤ) (z : Point) : Prop where
  denominatorX : ¬(p : ℤ) ∣ z.1 1
  denominatorY : ¬(p : ℤ) ∣ z.2 1
  residueX : (p : ℤ) ∣ z.1 0 - a * z.1 1
  residueY : (p : ℤ) ∣ z.2 0 - b * z.2 1
  equation : MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
    (IntegerFactorProjectiveCurve.projective G) = 0

def entry (H J : ℕ) (z : Point) (i : Exponent H J) : ℤ :=
  z.1 0 ^ i.1.val * z.1 1 ^ (H - i.1.val) * z.2 0 ^ i.2.val * z.2 1 ^ (J - i.2.val)

theorem minor_vanishing (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : Finset Point)
    (hclass : ∀ z ∈ S, ClassPoint p G a b z)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y)
    (hsmall : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2))
    (f : Exponent H J → S) :
    (Matrix.of (fun i j ↦ (entry H J (f i).val j : ℚ))).det = 0 := by
  have hcard : Fintype.card (Exponent H J) = (H + 1) * (J + 1) := by
    simp only [Exponent, Fintype.card_prod, Fintype.card_fin]
  have hz := ProjectiveDeterminantVanishing.vanishing p hp G a b hG hder H J
    (fun i : Exponent H J ↦ i.1.val) (fun i : Exponent H J ↦ i.2.val)
    (fun i ↦ by have := i.1.isLt; omega) (fun i ↦ by have := i.2.isLt; omega)
    L Y hL hY (fun i ↦ (f i).val.1) (fun i ↦ (f i).val.2)
    (fun i c ↦ hx _ (f i).property c) (fun i c ↦ hy _ (f i).property c)
    (fun i ↦ (hclass _ (f i).property).denominatorX)
    (fun i ↦ (hclass _ (f i).property).denominatorY)
    (fun i ↦ (hclass _ (f i).property).residueX)
    (fun i ↦ (hclass _ (f i).property).residueY)
    (fun i ↦ (hclass _ (f i).property).equation) (by simpa only [hcard] using hsmall)
  have ht : (Matrix.of (fun i j ↦ entry H J (f i).val j)).det = 0 := by
    have he : Matrix.of (fun i j ↦ entry H J (f i).val j) =
        (ProjectiveDeterminantVanishing.matrix H J
          (fun i : Exponent H J ↦ i.1.val) (fun i : Exponent H J ↦ i.2.val)
          (fun i ↦ (f i).val.1) (fun i ↦ (f i).val.2)).transpose := by
      ext i j
      rfl
    rw [he, Matrix.det_transpose]
    exact hz
  have hc := congrArg (fun z : ℤ ↦ (z : ℚ)) ht
  rw [Int.cast_det, Int.cast_zero] at hc
  exact hc

theorem exists_coefficients (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : Finset Point)
    (hclass : ∀ z ∈ S, ClassPoint p G a b z)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y)
    (hsmall : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2)) :
    ∃ w : Exponent H J → ℤ, w ≠ 0 ∧ ∀ z ∈ S, ∑ i, entry H J z i * w i = 0 := by
  classical
  let nH := (univ : Finset S).sup (fun z ↦
    (univ : Finset (Exponent H J)).sup (fun i ↦ (entry H J z.val i).natAbs)) + 1
  have hb (z : S) (i : Exponent H J) : |entry H J z.val i| ≤ (nH : ℤ) := by
    have h₁ := Finset.le_sup (f := fun i : Exponent H J ↦ (entry H J z.val i).natAbs)
      (Finset.mem_univ i)
    have h₂ := Finset.le_sup (f := fun z : S ↦
      (univ : Finset (Exponent H J)).sup (fun i ↦ (entry H J z.val i).natAbs))
      (Finset.mem_univ z)
    have hn : (entry H J z.val i).natAbs ≤ nH := (h₁.trans h₂).trans (Nat.le_succ _)
    have hc : (((entry H J z.val i).natAbs : ℕ) : ℤ) ≤ (nH : ℤ) := by exact_mod_cast hn
    simpa only [Int.natCast_natAbs] using hc
  have hn : 0 < Fintype.card (Exponent H J) := by
    simp only [Exponent, Fintype.card_prod, Fintype.card_fin]
    positivity
  obtain ⟨w, hw, _, hz⟩ := FiniteRowKernel.exists_integer_annihilator nH (by dsimp [nH]; omega)
    hn (fun z : S ↦ entry H J z.val) hb
    (minor_vanishing p hp G a b hG hder H J L Y hL hY S hclass hx hy hsmall)
  exact ⟨w, hw, fun z hzS ↦ hz ⟨z, hzS⟩⟩

theorem exists_auxiliary (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (S : Finset Point)
    (hclass : ∀ z ∈ S, ClassPoint p G a b z)
    (hx : ∀ z ∈ S, ∀ c, |(z.1 c : ℝ)| ≤ L)
    (hy : ∀ z ∈ S, ∀ c, |(z.2 c : ℝ)| ≤ Y)
    (hsmall : ((H + 1) * (J + 1)).factorial * (L ^ H * Y ^ J) ^ ((H + 1) * (J + 1)) <
      (p : ℝ) ^ (((H + 1) * (J + 1)) * ((H + 1) * (J + 1) - 1) / 2)) :
    ∃ F : ℤ[X][X], F ≠ 0 ∧ degreeX F ≤ H ∧ degreeY F ≤ J ∧
      ∀ z ∈ S, BivariateEvaluation.evaluate ((z.1 0 : ℚ) / z.1 1) ((z.2 0 : ℚ) / z.2 1) F = 0 ∧
        MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1 (IntegerFactorProjectiveCurve.projective F) = 0 := by
  obtain ⟨w, hw, hz⟩ := exists_coefficients p hp G a b hG hder H J L Y hL hY S hclass hx hy hsmall
  refine ⟨rectangle H J w, DeterminantAuxiliaryPolynomial.rectangle_ne_zero H J w hw,
    rectangle_degreeX H J w, rectangle_degreeY H J w, ?_⟩
  intro z hzS
  have hdenX : z.1 1 ≠ 0 := fun h ↦ (hclass z hzS).denominatorX (by rw [h]; exact dvd_zero _)
  have hdenY : z.2 1 ≠ 0 := fun h ↦ (hclass z hzS).denominatorY (by rw [h]; exact dvd_zero _)
  have he : MvPolynomial.eval₂ (MvPolynomial.eval z.2) z.1
      (DeterminantAuxiliaryBiform.biform H J w) = 0 := by
    rw [IntegerPairFactorCharts.evaluation_sum]
    calc
      _ = ∑ i, entry H J z i * w i := by
        apply Finset.sum_congr rfl
        intro i _
        unfold entry
        ring
      _ = 0 := hz z hzS
  have ha := (IntegerPairFactorCharts.rectangle_zero_iff H J w z.1 z.2 hdenX hdenY).mp he
  exact ⟨ha, (IntegerPairFactorCharts.projective_zero_iff _ z.1 z.2 hdenX hdenY).mpr ha⟩

end PaperP1.SmoothClassAuxiliary
