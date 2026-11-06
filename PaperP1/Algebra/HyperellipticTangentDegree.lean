module

public import PaperP1.Algebra.HyperellipticPoleDegree
public import PaperP1.Algebra.HyperellipticTangentDerivation
public import PaperP1.Algebra.DerivationPowerEvaluation

/-! # Exact uniform degree growth of tangent derivatives and their iterates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticTangentDegree

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree
open HyperellipticTangentDerivation DerivationPowerEvaluation
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

theorem derivative_degree_step (P : F[X]) (hP : P.derivative ≠ 0) :
    P.derivative.natDegree + 1 ≤ P.natDegree := by
  have hp : P.natDegree ≠ 0 := by
    intro hz
    exact hP (Polynomial.derivative_of_natDegree_zero hz)
  exact Nat.succ_le_of_lt (Polynomial.natDegree_derivative_lt hp)

theorem coefficient_two_degree (P : F[X]) : (2 * P).natDegree ≤ P.natDegree := by
  change (C (2 : F) * P).natDegree ≤ P.natDegree
  exact Polynomial.natDegree_C_mul_le _ _

theorem tangent_bound (f : F[X]) (hodd : Odd f.natDegree) (hd : 1 ≤ f.natDegree)
    (L : ℕ) (z : CurveRing f) (hz : poleDegree f z ≤ L) :
    poleDegree f (tangent f z) ≤ L + (f.natDegree - 2) := by
  obtain ⟨hzA, hzB⟩ := (coordinates_iff f hodd z L).mp hz
  apply (coordinates_iff f hodd _ _).mpr
  constructor
  · rw [tangent_re]
    by_cases hB : z.im = 0
    · simp only [hB, derivative_zero, mul_zero, add_zero, natDegree_zero, Nat.zero_le]
    · have hBdeg := hzB.resolve_left hB
      have hfirst : 2 * (f.derivative * z.im).natDegree ≤ L + (f.natDegree - 2) := by
        have hm := Polynomial.natDegree_mul_le (p := f.derivative) (q := z.im)
        have hdf := Polynomial.natDegree_derivative_le f
        omega
      have hsecond : 2 * (2 * f * z.im.derivative).natDegree ≤ L + (f.natDegree - 2) := by
        by_cases hBd : z.im.derivative = 0
        · simp only [hBd, mul_zero, natDegree_zero, Nat.zero_le]
        · have hm : (2 * f * z.im.derivative).natDegree ≤ f.natDegree + z.im.derivative.natDegree := by
            calc
              _ = (2 * (f * z.im.derivative)).natDegree := by rw [mul_assoc]
              _ ≤ (f * z.im.derivative).natDegree := coefficient_two_degree _
              _ ≤ _ := Polynomial.natDegree_mul_le
          have hs := derivative_degree_step z.im hBd
          omega
      have hadd := Polynomial.natDegree_add_le (f.derivative * z.im) (2 * f * z.im.derivative)
      omega
  · rw [tangent_im]
    by_cases hA : z.re.derivative = 0
    · exact Or.inl (by rw [hA, mul_zero])
    · right
      have hc := coefficient_two_degree z.re.derivative
      have hs := derivative_degree_step z.re hA
      omega

theorem iterate_bound (f : F[X]) (hodd : Odd f.natDegree) (hd : 1 ≤ f.natDegree)
    (L : ℕ) (z : CurveRing f) (hz : poleDegree f z ≤ L) (r : ℕ) :
    poleDegree f (iter
      (tangent f) r z) ≤ L + r * (f.natDegree - 2) := by
  induction r with
  | zero => simpa only [iter_zero, Nat.zero_mul, Nat.add_zero] using hz
  | succ r ih =>
    rw [iter_succ_left]
    have hh := tangent_bound f hodd hd (L + r * (f.natDegree - 2)) _ ih
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hh


end PaperP1.HyperellipticTangentDegree
