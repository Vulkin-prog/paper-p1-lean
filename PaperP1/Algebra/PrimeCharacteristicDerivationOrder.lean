module

public import PaperP1.Algebra.DerivationPowerEvaluation
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Nat.Prime.Factorial

/-! # Below the prime characteristic, factorials preserve the exact derivation order -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeCharacteristicDerivationOrder

open DerivationPowerEvaluation

theorem factorial_ne_zero {K : Type*} [CommRing K] (p : ℕ) [CharP K p]
    (hp : p.Prime) (n : ℕ) (hn : n < p) : (n.factorial : K) ≠ 0 := by
  intro hz
  have hd : p ∣ n.factorial := (CharP.cast_eq_zero_iff K p _).mp hz
  exact (Nat.not_le_of_lt hn) (hp.dvd_factorial.mp hd)

theorem evaluation_ne_zero {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing K] [IsDomain K] (p : ℕ) [CharP K p] (hp : p.Prime)
    (D : Derivation R A A) (ε : A →+* K) (a b : A) (ha : ε a = 0)
    (hDa : ε (D a) ≠ 0) (hb : ε b ≠ 0) (n : ℕ) (hn : n < p) :
    ε (iter D n (a ^ n * b)) ≠ 0 :=
  DerivationPowerEvaluation.evaluation_ne_zero D ε a ha n b (factorial_ne_zero p hp n hn) hDa hb

theorem power_order_lower_bound {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing K] [IsDomain K] (p : ℕ) [CharP K p] (hp : p.Prime)
    (D : Derivation R A A) (ε : A →+* K) (a b : A) (ha : ε a = 0)
    (hDa : ε (D a) ≠ 0) (hb : ε b ≠ 0) (m n : ℕ) (hm : m ≤ p)
    (hvanish : ∀ r < m, ε (iter D r (a ^ n * b)) = 0) : m ≤ n :=
  DerivationPowerEvaluation.power_order_lower_bound D ε a b ha hDa hb m n
    (fun r hr ↦ factorial_ne_zero p hp r (lt_of_lt_of_le hr hm)) hvanish

end PaperP1.PrimeCharacteristicDerivationOrder
