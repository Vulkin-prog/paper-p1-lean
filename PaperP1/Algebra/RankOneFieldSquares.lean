module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-! # A field extension of actual degree one reflects square roots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RankOneFieldSquares

theorem equiv_isSquare_iff {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    (e : R ≃ₐ[R] S) (a : R) : IsSquare (algebraMap R S a) ↔ IsSquare a := by
  have he (x : R) : e x = algebraMap R S x := e.commutes x
  rw [← he]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_mul, e.apply_symm_apply]
    exact hb
  · exact fun hs ↦ hs.map e.toRingHom

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem bijective (h : Module.finrank K L = 1) : Function.Bijective (algebraMap K L) :=
  Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h

def equiv (h : Module.finrank K L = 1) : K ≃ₐ[K] L :=
  AlgEquiv.ofBijective (Algebra.ofId K L) (bijective h)

theorem isSquare_iff (h : Module.finrank K L = 1) (a : K) :
    IsSquare (algebraMap K L a) ↔ IsSquare a := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (bijective h).surjective b
    refine ⟨c, (algebraMap K L).injective ?_⟩
    rw [map_mul, hc]
    exact hb
  · exact fun hs ↦ hs.map (algebraMap K L)

theorem quadratic_descent (h : Module.finrank K L = 1) (a : K) (b : L)
    (hb : b ^ 2 = algebraMap K L a) : ∃ c : K, c ^ 2 = a := by
  obtain ⟨c, hc⟩ := (bijective h).surjective b
  refine ⟨c, (algebraMap K L).injective ?_⟩
  rw [map_pow, hc]
  exact hb

end PaperP1.RankOneFieldSquares
