module

public import PaperP1.Algebra.PrimeCharacteristicDerivationOrder
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Actual polynomial root multiplicity follows from vanishing iterated tangent derivatives -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialDerivationMultiplicity

open Polynomial DerivationPowerEvaluation

theorem power_dvd_of_iterates {F : Type*} [Field F] (p : ℕ) [CharP F p] (hp : p.Prime)
    (D : Derivation F F[X] F[X]) (x : F) (hDX : (D X).eval x ≠ 0)
    (P : F[X]) (m : ℕ) (hm : m ≤ p)
    (hvanish : ∀ r < m, (iter D r P).eval x = 0) : (X - C x) ^ m ∣ P := by
  by_cases hP : P = 0
  · rw [hP]
    exact dvd_zero _
  obtain ⟨Q, hQ, hnot⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP x
  have hQeval : Q.eval x ≠ 0 := by
    intro hz
    exact hnot (dvd_iff_isRoot.mpr hz)
  have hzero : (evalRingHom x) (X - C x) = 0 := by simp
  have hDconst : D (C x) = 0 := by
    change D (algebraMap F F[X] x) = 0
    exact D.map_algebraMap x
  have hnonzero : (evalRingHom x) (D (X - C x)) ≠ 0 := by
    rw [map_sub, hDconst, sub_zero]
    exact hDX
  have horder := PrimeCharacteristicDerivationOrder.power_order_lower_bound p hp D
    (evalRingHom x) (X - C x) Q hzero hnonzero hQeval m (rootMultiplicity x P) hm (by
      intro r hr
      rw [← hQ]
      exact hvanish r hr)
  exact (le_rootMultiplicity_iff hP).mp horder

theorem multiplicity_lower_bound {F : Type*} [Field F] (p : ℕ) [CharP F p] (hp : p.Prime)
    (D : Derivation F F[X] F[X]) (x : F) (hDX : (D X).eval x ≠ 0)
    (P : F[X]) (hP : P ≠ 0) (m : ℕ) (hm : m ≤ p)
    (hvanish : ∀ r < m, (iter D r P).eval x = 0) : m ≤ rootMultiplicity x P :=
  (le_rootMultiplicity_iff hP).mpr (power_dvd_of_iterates p hp D x hDX P m hm hvanish)

end PaperP1.PolynomialDerivationMultiplicity
