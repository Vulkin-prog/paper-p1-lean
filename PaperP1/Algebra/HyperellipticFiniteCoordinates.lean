module

public import PaperP1.Algebra.HyperellipticPureFunctions
public import PaperP1.Algebra.HyperellipticTangentDegree

/-! # Actual finite coordinate extraction detects every function in the proved degree range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticFiniteCoordinates

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree
open HyperellipticPureFunctions HyperellipticMonomialIndex
open scoped QuadraticAlgebra Classical

variable {F : Type*} [Field F]

def coefficient (f : F[X]) (L : ℕ) : Index f.natDegree L → (CurveRing f →ₗ[F] F)
  | Sum.inl i => realCoefficient f i.val
  | Sum.inr j => imaginaryCoefficient f j.val

def extract (f : F[X]) (L : ℕ) : CurveRing f →ₗ[F] (Index f.natDegree L → F) :=
  LinearMap.pi (coefficient f L)

theorem zero_of_coefficients (f : F[X]) (hodd : Odd f.natDegree) (L : ℕ) (z : CurveRing f)
    (hL : poleDegree f z ≤ L) (hc : ∀ i, coefficient f L i z = 0) : z = 0 := by
  obtain ⟨hre, him⟩ := (coordinates_iff f hodd z L).mp hL
  apply (zero_iff f z).mpr
  constructor
  · apply Polynomial.ext
    intro n
    change z.re.coeff n = 0
    by_cases hn : n < L / 2 + 1
    · exact hc (Sum.inl ⟨n, hn⟩)
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  · rcases him with him | him
    · exact him
    · have hd : f.natDegree ≤ L := by omega
      apply Polynomial.ext
      intro n
      change z.im.coeff n = 0
      by_cases hn : n < (L - f.natDegree) / 2 + 1
      · have hb : n < (if f.natDegree ≤ L then (L - f.natDegree) / 2 + 1 else 0) := by
          rw [ite_eq_left hd]
          exact hn
        exact hc (Sum.inr ⟨n, hb⟩)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem extract_zero_iff (f : F[X]) (hodd : Odd f.natDegree) (L : ℕ) (z : CurveRing f)
    (hL : poleDegree f z ≤ L) : extract f L z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply zero_of_coefficients f hodd L z hL
    intro i
    exact congrFun hz i
  · rintro rfl
    exact map_zero _

end PaperP1.HyperellipticFiniteCoordinates
