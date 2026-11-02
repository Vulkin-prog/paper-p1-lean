module

public import PaperP1.Algebra.BivariateDegrees
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # A vanishing nonzero polynomial has an actual vanishing irreducible factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IrreduciblePointFactor

open Polynomial PaperP1.BivariateDegrees

theorem exists_factor {R S : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [IsDomain S] (φ : R →+* S) (P : R) (hP : P ≠ 0) (hz : φ P = 0) :
    ∃ C₀ : R, Irreducible C₀ ∧ C₀ ∣ P ∧ φ C₀ = 0 := by
  induction P using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hP rfl).elim
  | unit u hu => exact ((hu.map φ).ne_zero hz).elim
  | mul a i ha hi ih =>
    rw [map_mul] at hz
    rcases mul_eq_zero.mp hz with hiz | haz
    · exact ⟨i, hi, ⟨a, rfl⟩, hiz⟩
    · obtain ⟨C₀, hC, hdiv, hzero⟩ := ih ha haz
      exact ⟨C₀, hC, dvd_mul_of_dvd_right hdiv i, hzero⟩

theorem integer_point (P : ℤ[X][X]) (hP : P ≠ 0) (x y : ℤ) (hz : P.evalEval x y = 0) :
    ∃ C₀ : ℤ[X][X], Irreducible C₀ ∧ C₀ ∣ P ∧ C₀.evalEval x y = 0 :=
  exists_factor (Polynomial.evalEvalRingHom x y) P hP hz

theorem factor_partial_degrees (P C₀ : ℤ[X][X]) (hP : P ≠ 0) (hdiv : C₀ ∣ P) :
    degreeX C₀ ≤ degreeX P ∧ degreeY C₀ ≤ degreeY P := by
  obtain ⟨D, hD⟩ := hdiv
  rw [hD] at hP ⊢
  exact factor_partial_degrees_le C₀ D hP

end PaperP1.IrreduciblePointFactor
