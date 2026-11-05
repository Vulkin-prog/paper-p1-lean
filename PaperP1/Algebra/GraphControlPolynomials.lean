module

public import PaperP1.Algebra.RationalTangentNumerator
public import PaperP1.Algebra.PlaneCoordinateSwap
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.FinCases

/-! # Concrete graph-control equations in both orientations

Ten static equations control partials, slopes and square boundaries. The
remaining equations are the exact positive-order graph derivative numerators.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GraphControlPolynomials

open MvPolynomial PlaneCoordinateSwap RationalTangentNumerator PolynomialTangentDegree

def static (P : MvPolynomial (Fin 2) ℝ) (i : Fin 10) : MvPolynomial (Fin 2) ℝ :=
  match i.val with
  | 0 => pderiv 0 P
  | 1 => pderiv 1 P
  | 2 => pderiv 0 P + pderiv 1 P
  | 3 => pderiv 0 P - pderiv 1 P
  | 4 => X 0 - 1
  | 5 => X 0 + 1
  | 6 => X 1 - 1
  | 7 => X 1 + 1
  | 8 => X 0
  | _ => X 1

def orientedNumerator (P : MvPolynomial (Fin 2) ℝ) (i : Fin 2) (n : ℕ) :
    MvPolynomial (Fin 2) ℝ :=
  if i = 0 then numerator P (X 1) n else polynomial (numerator (polynomial P) (X 1) n)

def family (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) :
    Fin 10 ⊕ (Fin 2 × Fin r) → MvPolynomial (Fin 2) ℝ :=
  Sum.elim (static P) (fun j ↦ orientedNumerator P j.1 j.2.val)

@[simp] theorem static_zero (P : MvPolynomial (Fin 2) ℝ) : static P 0 = pderiv 0 P := rfl

@[simp] theorem static_one (P : MvPolynomial (Fin 2) ℝ) : static P 1 = pderiv 1 P := rfl

theorem static_degree (P : MvPolynomial (Fin 2) ℝ) (i : Fin 10) :
    (static P i).totalDegree ≤ max P.totalDegree 1 := by
  have h0 := pderiv_degree_le P 0
  have h1 := pderiv_degree_le P 1
  have hlinear (j : Fin 2) :
      (X j - 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ max P.totalDegree 1 ∧
      (X j + 1 : MvPolynomial (Fin 2) ℝ).totalDegree ≤ max P.totalDegree 1 := by
    constructor
    · exact (totalDegree_sub _ _).trans (by
        simpa only [totalDegree_X, totalDegree_one, max_zero] using le_max_right P.totalDegree 1)
    · exact (totalDegree_add _ _).trans (by
        simpa only [totalDegree_X, totalDegree_one, max_zero] using le_max_right P.totalDegree 1)
  fin_cases i <;> simp only [static]
  · exact h0.trans (le_max_left _ _)
  · exact h1.trans (le_max_left _ _)
  · exact (totalDegree_add _ _).trans ((max_le h0 h1).trans (le_max_left _ _))
  · exact (totalDegree_sub _ _).trans ((max_le h0 h1).trans (le_max_left _ _))
  · exact (hlinear 0).1
  · exact (hlinear 0).2
  · exact (hlinear 1).1
  · exact (hlinear 1).2
  · simpa only [totalDegree_X] using le_max_right P.totalDegree 1
  · simpa only [totalDegree_X] using le_max_right P.totalDegree 1

theorem oriented_degree (P : MvPolynomial (Fin 2) ℝ) (i : Fin 2) (n : ℕ) :
    (orientedNumerator P i n).totalDegree ≤ 1 + 2 * P.totalDegree * (n + 1) := by
  fin_cases i
  · simpa [orientedNumerator, totalDegree_X] using numerator_degree P (X 1) n
  · simpa [orientedNumerator, totalDegree_X] using numerator_degree (polynomial P) (X 1) n

theorem family_degree (P : MvPolynomial (Fin 2) ℝ) (r : ℕ)
    (i : Fin 10 ⊕ (Fin 2 × Fin r)) :
    (family P r i).totalDegree ≤ 1 + 2 * P.totalDegree * (r + 1) := by
  cases i with
  | inl i =>
    change (static P i).totalDegree ≤ _
    apply (static_degree P i).trans
    apply max_le
    · have hr : 1 ≤ r + 1 := by omega
      have hh := Nat.mul_le_mul_left P.totalDegree hr
      nlinarith
    · omega
  | inr i =>
    change (orientedNumerator P i.1 i.2.val).totalDegree ≤ _
    exact (oriented_degree P i.1 i.2.val).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left (2 * P.totalDegree) (by omega)) 1)

theorem sum_degree (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) :
    (∑ i, (family P r i).totalDegree) ≤ (10 + 2 * r) * (1 + 2 * P.totalDegree * (r + 1)) := by
  let b := 1 + 2 * P.totalDegree * (r + 1)
  have hb : ∀ i : Fin 10 ⊕ (Fin 2 × Fin r), (family P r i).totalDegree ≤ b := family_degree P r
  calc
    _ ≤ ∑ _i : Fin 10 ⊕ (Fin 2 × Fin r), b := Finset.sum_le_sum (fun i _hi ↦ hb i)
    _ = Fintype.card (Fin 10 ⊕ (Fin 2 × Fin r)) * b := by simp
    _ = _ := by simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, b]

theorem bezout_budget (P : MvPolynomial (Fin 2) ℝ) (hD : 0 < P.totalDegree) (r : ℕ) :
    P.totalDegree * (∑ i, (family P r i).totalDegree) ≤ 30 * P.totalDegree ^ 2 * (r + 1) ^ 2 := by
  have hsize : 10 + 2 * r ≤ 10 * (r + 1) := by omega
  have hscale : 1 + 2 * P.totalDegree * (r + 1) ≤ 3 * P.totalDegree * (r + 1) := by
    have hh : 1 ≤ P.totalDegree * (r + 1) := Nat.mul_pos hD (by omega)
    nlinarith
  calc
    _ ≤ P.totalDegree * ((10 + 2 * r) * (1 + 2 * P.totalDegree * (r + 1))) :=
      Nat.mul_le_mul_left _ (sum_degree P r)
    _ ≤ P.totalDegree * ((10 * (r + 1)) * (3 * P.totalDegree * (r + 1))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hsize hscale)
    _ = _ := by ring

end PaperP1.GraphControlPolynomials
