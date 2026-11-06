module

public import PaperP1.Arithmetic.SmoothIntegerCongruenceBranch
public import PaperP1.Algebra.TernaryNilpotentImplicitFunction

/-! # One integer polynomial in two variables on an actual smooth surface residue class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothIntegerSurfaceBranch

open Polynomial

theorem implicit_mod_prime_power (p N : ℕ) (hp : p.Prime) (P : ℤ[X][X][X]) (a b c : ℤ)
    (hP : (p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P)
    (hder : ¬(p : ℤ) ∣ TernaryPolynomialEvaluation.evaluation a b c P.derivative) :
    ∃ q : ℤ[X][X], ∀ x y z : ℤ,
      (p : ℤ) ∣ x - a → (p : ℤ) ∣ y - b → (p : ℤ) ∣ z - c →
      TernaryPolynomialEvaluation.evaluation x y z P = 0 →
        (p : ℤ) ^ N ∣ z - q.evalEval (x - a) (y - b) := by
  let R := ZMod (p ^ N)
  let φ : ℤ →+* R := Int.castRingHom R
  let Q : R[X][X][X] := P.map (Polynomial.mapRingHom (Polynomial.mapRingHom φ))
  let I : Ideal R := Ideal.span {(p : R)}
  have hnil : I ^ N = ⊥ := by
    dsimp only [I]
    rw [Ideal.span_singleton_pow]
    have hz : (p : R) ^ N = 0 := by
      rw [← Nat.cast_pow]
      exact ZMod.natCast_self _
    rw [hz, Ideal.span_singleton_zero]
  have heval (x y z : ℤ) : TernaryPolynomialEvaluation.evaluation (φ x) (φ y) (φ z) Q =
      φ (TernaryPolynomialEvaluation.evaluation x y z P) :=
    TernaryPolynomialEvaluation.map_coefficients φ P x y z
  have hdeval : TernaryPolynomialEvaluation.evaluation (φ a) (φ b) (φ c) Q.derivative =
      φ (TernaryPolynomialEvaluation.evaluation a b c P.derivative) := by
    dsimp only [Q]
    rw [Polynomial.derivative_map]
    exact TernaryPolynomialEvaluation.map_coefficients φ P.derivative a b c
  have hmem (z : ℤ) (hz : (p : ℤ) ∣ z) : φ z ∈ I := by
    apply Ideal.mem_span_singleton.mpr
    simpa only [map_natCast] using map_dvd φ hz
  have hroot : TernaryPolynomialEvaluation.evaluation (φ a) (φ b) (φ c) Q ∈ I := by
    rw [heval]
    exact hmem _ hP
  have hunit : IsUnit (TernaryPolynomialEvaluation.evaluation (φ a) (φ b) (φ c) Q.derivative) := by
    rw [hdeval]
    exact SmoothIntegerCongruenceBranch.unit_mod_prime_power p N hp _ hder
  obtain ⟨q₀, hq₀⟩ := TernaryNilpotentImplicitFunction.exists_polynomial_implicit I N hnil
    Q (φ a) (φ b) (φ c) hroot (hunit.map (Ideal.Quotient.mk I))
  have hsurj : Function.Surjective φ := ZMod.intCast_surjective
  have hsurjPoly : Function.Surjective (Polynomial.mapRingHom φ) :=
    Polynomial.map_surjective φ hsurj
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (Polynomial.mapRingHom φ) hsurjPoly q₀
  refine ⟨q, ?_⟩
  intro x y z hx hy hz hzero
  have hxI : φ x - φ a ∈ I := by rw [← map_sub]; exact hmem _ hx
  have hyI : φ y - φ b ∈ I := by rw [← map_sub]; exact hmem _ hy
  have hzI : φ z - φ c ∈ I := by rw [← map_sub]; exact hmem _ hz
  have hQzero : TernaryPolynomialEvaluation.evaluation (φ x) (φ y) (φ z) Q = 0 := by
    rw [heval, hzero, map_zero]
  have hvalue := hq₀ (φ x) (φ y) (φ z) hxI hyI hzI hQzero
  have he : φ z = φ (q.evalEval (x - a) (y - b)) := by
    rw [hvalue, ← hq, ← map_sub, ← map_sub]
    exact Polynomial.map_mapRingHom_evalEval φ q (x - a) (y - b)
  have hzero' : φ (z - q.evalEval (x - a) (y - b)) = 0 := by
    rw [map_sub, he, sub_self]
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd
    (z - q.evalEval (x - a) (y - b)) (p ^ N)).mp hzero'
  simpa only [Nat.cast_pow] using hd

end PaperP1.SmoothIntegerSurfaceBranch
