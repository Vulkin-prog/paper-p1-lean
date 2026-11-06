module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-! # Exact evaluation of iterated derivations at a power of a vanishing element -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DerivationPowerEvaluation

variable {R A K : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing K]

def iter (D : Derivation R A A) (n : ℕ) : Module.End R A := D.toLinearMap ^ n

theorem iter_zero (D : Derivation R A A) (a : A) : iter D 0 a = a := rfl

theorem iter_succ_left (D : Derivation R A A) (n : ℕ) (a : A) :
    iter D (n + 1) a = D (iter D n a) := by
  simp only [iter, pow_succ', Module.End.mul_apply]
  rfl

theorem iter_succ_right (D : Derivation R A A) (n : ℕ) (a : A) :
    iter D (n + 1) a = iter D n (D a) := by
  simp only [iter, pow_succ, Module.End.mul_apply]
  rfl

theorem derivative_power_succ (D : Derivation R A A) (n : ℕ) (a b : A) :
    D (a ^ (n + 1) * b) = (n + 1) • (a ^ n * (D a * b)) + a ^ (n + 1) * D b := by
  rw [D.leibniz, D.leibniz_pow]
  simp only [show n + 1 - 1 = n by omega, smul_eq_mul, nsmul_eq_mul]
  ring

theorem power_dvd_derivative (D : Derivation R A A) (n : ℕ) (a b : A) :
    a ^ (n - 1) ∣ D (a ^ n * b) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [show n + 1 - 1 = n by omega, derivative_power_succ]
    refine ⟨(n + 1 : A) * D a * b + a * D b, ?_⟩
    simp only [nsmul_eq_mul, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem iter_power_dvd (D : Derivation R A A) (a b : A) (n r : ℕ) (hr : r ≤ n) :
    a ^ (n - r) ∣ iter D r (a ^ n * b) := by
  induction r with
  | zero => exact ⟨b, rfl⟩
  | succ r ih =>
    obtain ⟨q, hq⟩ := ih (by omega)
    rw [iter_succ_left, hq]
    have hd := power_dvd_derivative D (n - r) a q
    simpa only [show n - r - 1 = n - (r + 1) by omega] using hd

theorem evaluation_vanishes (D : Derivation R A A) (ε : A →+* K) (a b : A)
    (ha : ε a = 0) (n r : ℕ) (hr : r < n) : ε (iter D r (a ^ n * b)) = 0 := by
  obtain ⟨q, hq⟩ := iter_power_dvd D a b n r (by omega)
  rw [hq, map_mul, map_pow, ha, zero_pow (Nat.sub_pos_of_lt hr).ne', zero_mul]

theorem evaluation_exact_order (D : Derivation R A A) (ε : A →+* K) (a : A)
    (ha : ε a = 0) (n : ℕ) (b : A) :
    ε (iter D n (a ^ n * b)) = (n.factorial : K) * (ε (D a)) ^ n * ε b := by
  induction n generalizing b with
  | zero => simp only [iter_zero, pow_zero, one_mul, Nat.factorial_zero, Nat.cast_one]
  | succ n ih =>
    rw [iter_succ_right, derivative_power_succ]
    simp only [map_add, map_nsmul]
    rw [ih (D a * b), evaluation_vanishes D ε a (D b) ha (n + 1) n (Nat.lt_succ_self n)]
    simp only [map_mul, nsmul_eq_mul, add_zero, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

variable [IsDomain K]

theorem evaluation_ne_zero (D : Derivation R A A) (ε : A →+* K) (a : A)
    (ha : ε a = 0) (n : ℕ) (b : A) (hfactorial : (n.factorial : K) ≠ 0)
    (hDa : ε (D a) ≠ 0) (hb : ε b ≠ 0) : ε (iter D n (a ^ n * b)) ≠ 0 := by
  rw [evaluation_exact_order D ε a ha n b]
  exact mul_ne_zero (mul_ne_zero hfactorial (pow_ne_zero n hDa)) hb

theorem power_order_lower_bound (D : Derivation R A A) (ε : A →+* K) (a b : A)
    (ha : ε a = 0) (hDa : ε (D a) ≠ 0) (hb : ε b ≠ 0) (m n : ℕ)
    (hfactorial : ∀ r < m, (r.factorial : K) ≠ 0)
    (hvanish : ∀ r < m, ε (iter D r (a ^ n * b)) = 0) : m ≤ n := by
  by_contra hnot
  have hn : n < m := by omega
  exact evaluation_ne_zero D ε a ha n b (hfactorial n hn) hDa hb (hvanish n hn)

end PaperP1.DerivationPowerEvaluation
