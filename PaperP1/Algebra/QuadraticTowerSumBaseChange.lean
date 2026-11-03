module

public import PaperP1.Algebra.QuadraticTowerBaseChange
public import PaperP1.Algebra.FiniteRadicalProjection

/-! # The literal radical sum commutes with the actual recursive base change -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerSumBaseChange

open PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.QuadraticTowerBaseChange QuadraticAlgebra

theorem radicalSum_cons (R : Type*) [CommRing R] (a : R) (s : List R) :
    radicalSum R (a :: s) = root R (a :: s) 0 +
      algebraMap (Tower R s) (Tower R (a :: s)) (radicalSum R s) := by
  simp only [radicalSum, List.length_cons, Fin.sum_univ_succ, root_succ, map_sum]

theorem quadraticMap_omega {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    quadraticMap φ a b hab omega = omega := by
  ext <;> simp only [quadraticMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    re_omega, im_omega, map_zero, map_one]

theorem map_radicalSum {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : List R) :
    (mapData φ s).hom (radicalSum R s) = radicalSum S (s.map φ) := by
  induction s with
  | nil =>
    change (mapData φ []).hom (radicalSum R []) = radicalSum S []
    simp only [radicalSum, List.length_nil, Fin.sum_univ_zero, map_zero]
  | cons a s ih =>
    change quadraticMap (mapData φ s).hom (algebraMap R (Tower R s) a)
      (algebraMap S (Tower S (s.map φ)) (φ a)) ((mapData φ s).commutes a)
      (radicalSum R (a :: s)) = radicalSum S (φ a :: s.map φ)
    rw [radicalSum_cons, map_add, radicalSum_cons]
    change quadraticMap (mapData φ s).hom _ _ _ omega +
      quadraticMap (mapData φ s).hom _ _ _
        (algebraMap (Tower R s) (Tower R (a :: s)) (radicalSum R s)) = _
    rw [quadraticMap_omega, quadraticMap_base, ih, root_zero]

end PaperP1.QuadraticTowerSumBaseChange
