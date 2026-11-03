module

public import PaperP1.Algebra.QuadraticUniversalMap
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Ring.Parity

/-! # Every field extension of odd actual degree reflects squares, in every characteristic -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OddDegreeFieldSquares

variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem two_dvd_degree (a : K) (ha : ¬ IsSquare a) (hsq : IsSquare (algebraMap K E a)) :
    2 ∣ Module.finrank K E := by
  obtain ⟨r, hr⟩ := hsq
  have hroot : r ^ 2 = algebraMap K E a := by simpa only [pow_two] using hr.symm
  let : Fact (¬ IsSquare a) := ⟨ha⟩
  let φ : QuadraticAlgebra K a 0 →ₐ[K] E :=
    { toRingHom := QuadraticUniversalMap.liftRing (algebraMap K E) a r hroot
      commutes' := QuadraticUniversalMap.liftRing_base (algebraMap K E) a r hroot }
  let : Algebra (QuadraticAlgebra K a 0) E := φ.toRingHom.toAlgebra
  have : IsScalarTower K (QuadraticAlgebra K a 0) E :=
    IsScalarTower.of_algebraMap_eq (fun b ↦ (φ.commutes b).symm)
  have h := Module.finrank_dvd_finrank_right K (QuadraticAlgebra K a 0) E
  rw [QuadraticAlgebra.finrank_eq_two] at h
  exact h

theorem isSquare_iff (hdegree : Odd (Module.finrank K E)) (a : K) :
    IsSquare (algebraMap K E a) ↔ IsSquare a := by
  constructor
  · intro hsq
    by_contra ha
    exact hdegree.not_two_dvd_nat (two_dvd_degree a ha hsq)
  · exact fun hsq ↦ hsq.map (algebraMap K E)

theorem quadratic_descent (hdegree : Odd (Module.finrank K E)) (a : K) (r : E)
    (hroot : r ^ 2 = algebraMap K E a) : ∃ b : K, b ^ 2 = a := by
  have hs := (isSquare_iff hdegree a).mp ⟨r, by simpa only [pow_two] using hroot.symm⟩
  obtain ⟨b, hb⟩ := hs
  exact ⟨b, by simpa only [pow_two] using hb.symm⟩

end PaperP1.OddDegreeFieldSquares
