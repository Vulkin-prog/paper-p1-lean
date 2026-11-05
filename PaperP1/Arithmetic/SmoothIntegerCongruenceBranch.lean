module

public import PaperP1.Algebra.BivariateNilpotentImplicitFunction
public import Mathlib.Data.ZMod.Units
public import Mathlib.RingTheory.Int.Basic

/-! # One integer polynomial describes all points in an actual smooth congruence class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothIntegerCongruenceBranch

open Polynomial

theorem unit_mod_prime_power (p N : ℕ) (hp : p.Prime) (D : ℤ) (hD : ¬(p : ℤ) ∣ D) :
    IsUnit (D : ZMod (p ^ N)) := by
  have hcop : p.Coprime D.natAbs := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    apply hD
    apply Int.natAbs_dvd_natAbs.mp
    simpa only [Int.natAbs_natCast] using hd
  apply (ZMod.isUnit_intCast_iff_isCoprime D (p ^ N)).mpr
  apply Int.isCoprime_iff_nat_coprime.mpr
  simpa only [Int.natAbs_natCast] using hcop.pow_left N

theorem implicit_mod_prime_power (p N : ℕ) (hp : p.Prime) (P : ℤ[X][X]) (a b : ℤ)
    (hP : (p : ℤ) ∣ P.evalEval a b) (hder : ¬(p : ℤ) ∣ P.derivative.evalEval a b) :
    ∃ q : ℤ[X], ∀ x y : ℤ, (p : ℤ) ∣ x - a → (p : ℤ) ∣ y - b → P.evalEval x y = 0 →
      (p : ℤ) ^ N ∣ y - q.eval (x - a) := by
  let R := ZMod (p ^ N)
  let φ : ℤ →+* R := Int.castRingHom R
  let Q : R[X][X] := P.map (Polynomial.mapRingHom φ)
  let I : Ideal R := Ideal.span {(p : R)}
  have hnil : I ^ N = ⊥ := by
    dsimp only [I]
    rw [Ideal.span_singleton_pow]
    have hz : (p : R) ^ N = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [hz, Ideal.span_singleton_zero]
  have heval (x y : ℤ) : Q.evalEval (φ x) (φ y) = φ (P.evalEval x y) :=
    Polynomial.map_mapRingHom_evalEval φ P x y
  have hdeval : Q.derivative.evalEval (φ a) (φ b) = φ (P.derivative.evalEval a b) := by
    dsimp only [Q]
    rw [Polynomial.derivative_map]
    exact Polynomial.map_mapRingHom_evalEval φ P.derivative a b
  have hmem (z : ℤ) (hz : (p : ℤ) ∣ z) : φ z ∈ I := by
    apply Ideal.mem_span_singleton.mpr
    simpa only [map_natCast] using map_dvd φ hz
  have hroot : Q.evalEval (φ a) (φ b) ∈ I := by
    rw [heval]
    exact hmem _ hP
  have hunit : IsUnit (Q.derivative.evalEval (φ a) (φ b)) := by
    rw [hdeval]
    exact unit_mod_prime_power p N hp _ hder
  obtain ⟨q₀, hq₀⟩ := BivariateNilpotentImplicitFunction.exists_polynomial_implicit I N hnil
    Q (φ a) (φ b) hroot (hunit.map (Ideal.Quotient.mk I))
  have hsurj : Function.Surjective φ := ZMod.intCast_surjective
  obtain ⟨q, hq⟩ := Polynomial.map_surjective φ hsurj q₀
  refine ⟨q, ?_⟩
  intro x y hx hy hzero
  have hxI : φ x - φ a ∈ I := by rw [← map_sub]; exact hmem _ hx
  have hyI : φ y - φ b ∈ I := by rw [← map_sub]; exact hmem _ hy
  have hQzero : Q.evalEval (φ x) (φ y) = 0 := by rw [heval, hzero, map_zero]
  have hvalue := hq₀ (φ x) (φ y) hxI hyI hQzero
  rw [← hq, ← map_sub, Polynomial.eval_map_apply] at hvalue
  have hz : φ (y - q.eval (x - a)) = 0 := by rw [map_sub, hvalue, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (y - q.eval (x - a)) (p ^ N)).mp hz
  simpa only [Nat.cast_pow] using hd

end PaperP1.SmoothIntegerCongruenceBranch
