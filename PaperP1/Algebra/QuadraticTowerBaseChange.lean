module

public import PaperP1.Algebra.FiniteQuadraticTower
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-! # Faithful base change on the actual iterated radical algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.QuadraticTowerBaseChange

open QuadraticAlgebra PaperP1.FiniteQuadraticTower

def quadraticMap {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) : QuadraticAlgebra R a 0 →+* QuadraticAlgebra S b 0 where
  toFun z := ⟨φ z.re, φ z.im⟩
  map_zero' := by ext <;> simp only [re_zero, im_zero, map_zero]
  map_one' := by ext <;> simp only [re_one, im_one, map_one, map_zero]
  map_add' z w := by ext <;> simp only [re_add, im_add, map_add]
  map_mul' z w := by
    ext <;> simp only [re_mul, im_mul, zero_mul, add_zero, map_add, map_mul, hab]

theorem quadraticMap_base {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) (r : R) :
    quadraticMap φ a b hab (algebraMap R (QuadraticAlgebra R a 0) r) =
      algebraMap S (QuadraticAlgebra S b 0) (φ r) := by
  ext <;> simp only [quadraticMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    algebraMap_re, algebraMap_im, map_zero]

theorem quadraticMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (a : R) (b : S) (hab : φ a = b) :
    Function.Injective (quadraticMap φ a b hab) := by
  intro z w hzw
  apply QuadraticAlgebra.ext
  · exact hφ (congrArg QuadraticAlgebra.re hzw)
  · exact hφ (congrArg QuadraticAlgebra.im hzw)

structure MapData {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) (s : List R) where
  hom : Tower R s →+* Tower S (s.map φ)
  commutes : ∀ r, hom (algebraMap R (Tower R s) r) = algebraMap S (Tower S (s.map φ)) (φ r)

def mapData {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S) : (s : List R) → MapData φ s
  | [] => { hom := φ, commutes := fun _ ↦ rfl }
  | a :: s =>
    let m := mapData φ s
    { hom := quadraticMap m.hom (algebraMap R (Tower R s) a)
        (algebraMap S (Tower S (s.map φ)) (φ a)) (m.commutes a)
      commutes := by
        intro r
        change quadraticMap _ _ _ _ (algebraMap (Tower R s) (Tower R (a :: s)) (algebraMap R (Tower R s) r)) = _
        rw [quadraticMap_base, m.commutes r]
        rfl }

theorem map_injective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (s : List R) : Function.Injective (mapData φ s).hom := by
  induction s with
  | nil => exact hφ
  | cons a s ih => exact quadraticMap_injective _ ih _ _ ((mapData φ s).commutes a)

theorem source_isDomain {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ) (s : List R)
    (htarget : IsDomain (Tower S (s.map φ))) : IsDomain (Tower R s) := by
  let := htarget
  exact (map_injective φ hφ s).isDomain (mapData φ s).hom

end PaperP1.QuadraticTowerBaseChange
