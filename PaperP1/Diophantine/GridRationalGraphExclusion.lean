module

public import PaperP1.Diophantine.GridRationalGraphBound
public import PaperP1.Diophantine.GridPolynomialGraphBound
public import PaperP1.Arithmetic.RationalGridLineObstruction

/-! # All positive-degree rational graphs fixed by an offset grid have bounded admissible comparable integral points -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GridRationalGraphExclusion

open Polynomial PaperP1.IntegralRationalInterpolation PaperP1.SelectedProportionalPairs

def bound (a B : ℕ) : ℕ := max (GridRationalGraphBound.bound a B) ((a + 2) * heightBound a B)

theorem integral_point (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B)
    (i j : Fin (2 * a + 1) → ℤ) (hinj : Function.Injective i)
    (hiB : ∀ t, (i t).natAbs ≤ B) (hjB : ∀ t, (j t).natAbs ≤ B)
    (S T : Finset ℤ) (hiS : ∀ t, i t ∈ S) (hjT : ∀ t, j t ∈ T)
    (p q : ℚ[X]) (hq0 : q ≠ 0) (hcop : IsCoprime p q) (hdegree : max p.natDegree q.natDegree = a)
    (hgrid : ∀ t, p.eval (-(i t : ℚ)) = -(j t : ℚ) * q.eval (-(i t : ℚ)))
    (X Y : ℤ) (hcomparable : Y.natAbs ≤ 2 * X.natAbs)
    (hpoint : p.eval (X : ℚ) = (Y : ℚ) * q.eval (X : ℚ))
    (hposS : ∀ z ∈ S, 0 < X + z) (hposT : ∀ z ∈ T, 0 < Y + z)
    (hind : EvenIndependentValues.Independent (values X S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values X S)) (FiniteEvenSquareClasses.space (values Y T))) :
    X.natAbs ≤ bound a B := by
  have hneg : Function.Injective (fun t ↦ -i t) := neg_injective.comp hinj
  have hx : ∀ t, (-i t).natAbs ≤ B := fun t ↦ (Int.natAbs_neg _).trans_le (hiB t)
  have hy : ∀ t, (-j t).natAbs ≤ B := fun t ↦ (Int.natAbs_neg _).trans_le (hjB t)
  have hgrid' : ∀ t, p.eval ((-i t : ℤ) : ℚ) = ((-j t : ℤ) : ℚ) * q.eval ((-i t : ℤ) : ℚ) := by
    simpa only [Int.cast_neg] using hgrid
  by_cases hqpos : 0 < q.natDegree
  · exact (GridRationalGraphBound.integral_point a B hB (fun t ↦ -i t) (fun t ↦ -j t) hneg hx hy
      p q hq0 hcop hdegree hqpos hgrid' X Y hpoint).trans (le_max_left _ _)
  · have hqdeg : q.natDegree = 0 := by omega
    by_cases ha2 : 2 ≤ a
    · exact (GridPolynomialGraphBound.integral_point a B ha2 hB (fun t ↦ -i t) (fun t ↦ -j t) hneg hx hy
        p q hq0 hcop hdegree hqdeg hgrid' X Y hcomparable hpoint).trans (le_max_right _ _)
    · have ha1 : a = 1 := by omega
      let t₀ : Fin (2 * a + 1) := ⟨0, by omega⟩
      let t₁ : Fin (2 * a + 1) := ⟨1, by omega⟩
      have hne : i t₀ ≠ i t₁ := fun hz ↦ (by decide : (0 : ℕ) ≠ 1)
        (congrArg Fin.val (hinj hz))
      have hp : p.natDegree ≤ 1 := by have := le_max_left p.natDegree q.natDegree; omega
      exact False.elim (RationalGridLineObstruction.rational_graph S T X Y (i t₀) (i t₁) (j t₀) (j t₁)
        (hiS t₀) (hiS t₁) (hjT t₀) (hjT t₁) hne hposS hposT hind hdirect
        p q hp hqdeg hq0 (hgrid t₀) (hgrid t₁) hpoint)

theorem bound_le_polynomial (a B : ℕ) (ha : 0 < a) (hB : 1 ≤ B) :
    bound a B ≤
      ((3 * ((2 * a + 1) + 1)) ^ (2 * a + 1) +
        (2 * a).factorial * ((3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)) ^ (2 * a) +
        (a + 2) * (3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)) *
      B ^ (((a + 1) * (2 * a + 1)) * (2 * a)) := by
  let C := (3 * ((2 * a + 1) + 1)) ^ (2 * a + 1)
  let E := (a + 1) * (2 * a + 1)
  change bound a B ≤ (C + (2 * a).factorial * C ^ (2 * a) + (a + 2) * C) * B ^ (E * (2 * a))
  have he : E ≤ E * (2 * a) := Nat.le_mul_of_pos_right E (by omega)
  have hheight : heightBound a B = C * B ^ E := heightBound_eq a B
  have hr := GridRationalGraphBound.bound_le_polynomial a B ha hB
  change GridRationalGraphBound.bound a B ≤ (C + (2 * a).factorial * C ^ (2 * a)) * B ^ (E * (2 * a)) at hr
  apply max_le
  · exact hr.trans (Nat.mul_le_mul_right _ (by omega))
  · calc
      (a + 2) * heightBound a B = ((a + 2) * C) * B ^ E := by rw [hheight]; ring
      _ ≤ ((a + 2) * C) * B ^ (E * (2 * a)) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB he)
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end PaperP1.GridRationalGraphExclusion
