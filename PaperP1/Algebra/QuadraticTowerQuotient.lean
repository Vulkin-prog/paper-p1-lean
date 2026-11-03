module

public import PaperP1.Algebra.QuadraticTowerBaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Base specialization of the literal quadratic tower is its actual coefficient quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerQuotient

open QuadraticAlgebra PaperP1.FiniteQuadraticTower PaperP1.QuadraticTowerBaseChange

variable {R S : Type*} [CommRing R] [CommRing S]

theorem quadraticMap_surjective (φ : R →+* S) (hφ : Function.Surjective φ)
    (a : R) (b : S) (hab : φ a = b) : Function.Surjective (quadraticMap φ a b hab) := by
  intro z
  obtain ⟨x, hx⟩ := hφ z.re
  obtain ⟨y, hy⟩ := hφ z.im
  exact ⟨⟨x, y⟩, QuadraticAlgebra.ext hx hy⟩

theorem quadraticMap_ker (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    RingHom.ker (quadraticMap φ a b hab) =
      (RingHom.ker φ).map (algebraMap R (QuadraticAlgebra R a 0)) := by
  apply le_antisymm
  · intro z hz
    have hre : φ z.re = 0 := congrArg QuadraticAlgebra.re (RingHom.mem_ker.mp hz)
    have him : φ z.im = 0 := congrArg QuadraticAlgebra.im (RingHom.mem_ker.mp hz)
    have h₁ := Ideal.mem_map_of_mem (algebraMap R (QuadraticAlgebra R a 0)) (RingHom.mem_ker.mpr hre)
    have h₂ := Ideal.mem_map_of_mem (algebraMap R (QuadraticAlgebra R a 0)) (RingHom.mem_ker.mpr him)
    have h := Ideal.add_mem ((RingHom.ker φ).map (algebraMap R (QuadraticAlgebra R a 0))) h₁
      (Ideal.mul_mem_right QuadraticAlgebra.omega _ h₂)
    have he : algebraMap R (QuadraticAlgebra R a 0) z.re +
        algebraMap R (QuadraticAlgebra R a 0) z.im * QuadraticAlgebra.omega = z := by
      ext <;> simp
    exact he ▸ h
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change quadraticMap φ a b hab (algebraMap R (QuadraticAlgebra R a 0) r) = 0
    rw [quadraticMap_base, RingHom.mem_ker.mp hr, map_zero]

theorem map_surjective (φ : R →+* S) (hφ : Function.Surjective φ) (s : List R) :
    Function.Surjective (mapData φ s).hom := by
  induction s with
  | nil => exact hφ
  | cons a s ih => exact quadraticMap_surjective _ ih _ _ ((mapData φ s).commutes a)

theorem map_ker (φ : R →+* S) (s : List R) :
    RingHom.ker (mapData φ s).hom = (RingHom.ker φ).map (algebraMap R (Tower R s)) := by
  induction s with
  | nil =>
    change RingHom.ker φ = (RingHom.ker φ).map (RingHom.id R)
    exact (Ideal.map_id (RingHom.ker φ)).symm
  | cons a s ih =>
    change RingHom.ker (quadraticMap (mapData φ s).hom (algebraMap R (Tower R s) a)
      (algebraMap S (Tower S (s.map φ)) (φ a)) ((mapData φ s).commutes a)) = _
    rw [quadraticMap_ker, ih, Ideal.map_map]
    rfl

def quotientEquiv (φ : R →+* S) (hφ : Function.Surjective φ) (s : List R) :
    (Tower R s) ⧸ (RingHom.ker φ).map (algebraMap R (Tower R s)) ≃+* Tower S (s.map φ) :=
  (Ideal.quotEquivOfEq (map_ker φ s).symm).trans
    ((mapData φ s).hom.quotientKerEquivOfSurjective (map_surjective φ hφ s))

theorem quotientEquiv_mk (φ : R →+* S) (hφ : Function.Surjective φ) (s : List R) (x : Tower R s) :
    quotientEquiv φ hφ s (Ideal.Quotient.mk _ x) = (mapData φ s).hom x := by
  rw [quotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end PaperP1.QuadraticTowerQuotient
