module

public import PaperP1.Algebra.HyperellipticPoleDegree

/-! # Actual quadratic polynomial monomials have distinct weights in odd degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticWeightedMonomials

open Polynomial HyperellipticPolynomialAlgebra HyperellipticPoleDegree
open scoped QuadraticAlgebra Classical

def weight (d : ℕ) : ℕ ⊕ ℕ → ℕ
  | Sum.inl i => 2 * i
  | Sum.inr j => d + 2 * j

def vector {F : Type*} [Field F] (f : F[X]) : ℕ ⊕ ℕ → CurveRing f
  | Sum.inl i => ⟨X ^ i, 0⟩
  | Sum.inr j => ⟨0, X ^ j⟩

theorem weight_injective (d : ℕ) (hodd : Odd d) : Function.Injective (weight d) := by
  obtain ⟨g, hg⟩ := hodd
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · have he : i = j := by dsimp only [weight] at hij; omega
    exact congrArg Sum.inl he
  · dsimp only [weight] at hij
    omega
  · dsimp only [weight] at hij
    omega
  · have he : i = j := by dsimp only [weight] at hij; omega
    exact congrArg Sum.inr he

theorem vector_ne_zero {F : Type*} [Field F] (f : F[X]) (i : ℕ ⊕ ℕ) : vector f i ≠ 0 := by
  rcases i with i | i
  · intro hz
    have hh := congrArg QuadraticAlgebra.re hz
    change (X : F[X]) ^ i = 0 at hh
    exact pow_ne_zero i X_ne_zero hh
  · intro hz
    have hh := congrArg QuadraticAlgebra.im hz
    change (X : F[X]) ^ i = 0 at hh
    exact pow_ne_zero i X_ne_zero hh

theorem vector_degree {F : Type*} [Field F] (f : F[X]) (hodd : Odd f.natDegree) (i : ℕ ⊕ ℕ) :
    poleDegree f (vector f i) = weight f.natDegree i := by
  rw [poleDegree, HyperellipticOddDegreeNorm.norm_natDegree f hodd]
  rcases i with i | i
  · change (if (0 : F[X]) = 0 then 2 * (X ^ i : F[X]).natDegree else
        max (2 * (X ^ i : F[X]).natDegree) (f.natDegree + 2 * (0 : F[X]).natDegree)) = 2 * i
    rw [ite_eq_left rfl, natDegree_pow, natDegree_X]
    simp only [Nat.mul_one]
  · have hn : (X : F[X]) ^ i ≠ 0 := pow_ne_zero i X_ne_zero
    change (if (X : F[X]) ^ i = 0 then 2 * (0 : F[X]).natDegree else
        max (2 * (0 : F[X]).natDegree) (f.natDegree + 2 * (X ^ i : F[X]).natDegree)) =
      f.natDegree + 2 * i
    rw [ite_eq_right hn, natDegree_zero, natDegree_pow, natDegree_X]
    simp only [Nat.mul_zero, Nat.mul_one, Nat.zero_max]

theorem power_ne_zero {F : Type*} [Field F] (f : F[X]) (hodd : Odd f.natDegree)
    (z : CurveRing f) (hz : z ≠ 0) (n : ℕ) : z ^ n ≠ 0 := by
  intro hzero
  have he := congrArg (fun u : CurveRing f ↦ QuadraticAlgebra.norm u) hzero
  rw [map_pow, QuadraticAlgebra.norm_zero] at he
  exact pow_ne_zero n (HyperellipticOddDegreeNorm.norm_ne_zero f hodd z hz) he

theorem product_power_degree {F : Type*} [Field F] (f : F[X]) (hodd : Odd f.natDegree)
    (i j : ℕ ⊕ ℕ) (p : ℕ) :
    poleDegree f (vector f i * vector f j ^ p) = weight f.natDegree i + p * weight f.natDegree j := by
  rw [mul_degree f hodd _ _ (vector_ne_zero f i) (power_ne_zero f hodd _ (vector_ne_zero f j) p),
    vector_degree f hodd i, pow_degree, vector_degree f hodd j]

end PaperP1.HyperellipticWeightedMonomials
