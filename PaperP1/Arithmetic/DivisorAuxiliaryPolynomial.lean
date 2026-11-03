module

public import PaperP1.Arithmetic.CoprimeRowDeterminants
public import PaperP1.Algebra.RectangularEvaluationPolynomial
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! # An actual bounded-degree auxiliary polynomial for coprime common divisors

The sole size condition below is an explicit finite inequality. No curve-point
count or polynomial-confinement conclusion is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DivisorAuxiliaryPolynomial

open Finset Matrix Polynomial PaperP1.RectangularEvaluationPolynomial

def integerRow (d : ℕ) (x y : ℤ) : Index d → ℤ := fun i ↦ x ^ i.1.val * y ^ i.2.val

theorem row_height (d B : ℕ) (hB : 1 ≤ B) (x y : ℤ)
    (hx : x.natAbs ≤ B) (hy : y.natAbs ≤ B) (i : Index d) :
    (integerRow d x y i).natAbs ≤ B ^ (2 * d) := by
  rw [integerRow, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
  calc
    _ ≤ B ^ i.1.val * B ^ i.2.val := Nat.mul_le_mul (Nat.pow_le_pow_left hx _) (Nat.pow_le_pow_left hy _)
    _ = B ^ (i.1.val + i.2.val) := (pow_add _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right hB (by have h1 := i.1.isLt; have h2 := i.2.isLt; omega)

theorem row_congruence (d : ℕ) (x y s t g : ℤ) (hs : g ∣ x + s) (ht : g ∣ y + t)
    (i : Index d) : g ∣ integerRow d s t i - integerRow d (-x) (-y) i := by
  have hs₀ : g ∣ s - -x := by simpa only [sub_neg_eq_add, add_comm] using hs
  have ht₀ : g ∣ t - -y := by simpa only [sub_neg_eq_add, add_comm] using ht
  have hsp := hs₀.trans (sub_dvd_pow_sub_pow s (-x) i.1.val)
  have htp := ht₀.trans (sub_dvd_pow_sub_pow t (-y) i.2.val)
  have he : integerRow d s t i - integerRow d (-x) (-y) i =
      (s ^ i.1.val - (-x) ^ i.1.val) * t ^ i.2.val +
        (-x) ^ i.1.val * (t ^ i.2.val - (-y) ^ i.2.val) := by unfold integerRow; ring
  rw [he]
  exact (dvd_mul_of_dvd_left hsp _).add (dvd_mul_of_dvd_right htp _)

theorem finite_confinement {ι : Type*} (d B X : ℕ) (hB : 1 ≤ B) (hX : 1 ≤ X)
    (x y : ℤ) (hx : x.natAbs ≤ X) (hy : y.natAbs ≤ X)
    (s t : ι → ℤ) (g : ι → ℕ) (Y : ℝ) (hY : 0 ≤ Y)
    (hcop : Pairwise (fun i j ↦ (g i).Coprime (g j)))
    (hs : ∀ i, (s i).natAbs ≤ B) (ht : ∀ i, (t i).natAbs ≤ B)
    (hdivs : ∀ i, (g i : ℤ) ∣ x + s i) (hdivt : ∀ i, (g i : ℤ) ∣ y + t i)
    (hlarge : ∀ i, Y ≤ (g i : ℝ))
    (hsize : (((Fintype.card (Index d)).factorial * X ^ (2 * d) *
        (B ^ (2 * d)) ^ (Fintype.card (Index d) - 1) : ℕ) : ℝ) <
          Y ^ (Fintype.card (Index d) - 1)) :
    ∃ P : ℚ[X][X], P ≠ 0 ∧ P.natDegree ≤ d ∧ (∀ b, (P.coeff b).natDegree ≤ d) ∧
      P.support.sup (fun b ↦ b + (P.coeff b).natDegree) ≤ 2 * d ∧
      ∀ i, P.evalEval (s i : ℚ) (t i : ℚ) = 0 := by
  classical
  apply exists_polynomial d (fun i ↦ (s i : ℚ)) (fun i ↦ (t i : ℚ))
  intro f hf
  let A : Matrix (Index d) (Index d) ℤ := fun i ↦ integerRow d (s (f i)) (t (f i))
  let v := integerRow d (-x) (-y)
  have hcopf : Pairwise (fun i j ↦ (g (f i)).Coprime (g (f j))) := fun i j hij ↦ hcop (fun he ↦ hij (hf he))
  have hrow (i j : Index d) : (g (f i) : ℤ) ∣ A i j - v j :=
    row_congruence d x y (s (f i)) (t (f i)) (g (f i)) (hdivs (f i)) (hdivt (f i)) j
  have hzero (r : Index d) : (A.updateRow r v).det = 0 := by
    apply CoprimeRowDeterminants.replacement_zero A v r (fun i ↦ g (f i)) hcopf hrow
      (X ^ (2 * d)) (B ^ (2 * d))
    · intro j
      exact row_height d X hX (-x) (-y) (by simpa only [Int.natAbs_neg] using hx)
        (by simpa only [Int.natAbs_neg] using hy) j
    · intro i j
      exact row_height d B hB (s (f i)) (t (f i)) (hs (f i)) (ht (f i)) j
    · have hp : Y ^ (Fintype.card (Index d) - 1) ≤
          ((∏ i ∈ univ.erase r, g (f i) : ℕ) : ℝ) := by
        calc
          _ = ∏ _i ∈ univ.erase r, Y := by simp
          _ ≤ ∏ i ∈ univ.erase r, (g (f i) : ℝ) :=
            Finset.prod_le_prod₀ (fun _ _ ↦ hY) (fun i _ ↦ hlarge (f i))
          _ = _ := by simp only [Nat.cast_prod]
      exact_mod_cast hsize.trans_le hp
  have hdet : A.det = 0 := CoprimeRowDeterminants.determinant_zero_of_replacements A v
    (0, 0) (by simp [v, integerRow]) hzero
  have hcast : (fun i j ↦ row d (s (f i) : ℚ) (t (f i) : ℚ) j) =
      (Int.castRingHom ℚ).mapMatrix A := by
    funext i j
    change (s (f i) : ℚ) ^ j.1.val * (t (f i) : ℚ) ^ j.2.val =
      ((s (f i) ^ j.1.val * t (f i) ^ j.2.val : ℤ) : ℚ)
    push_cast
    rfl
  rw [hcast, ← RingHom.map_det, hdet, map_zero]

end PaperP1.DivisorAuxiliaryPolynomial
