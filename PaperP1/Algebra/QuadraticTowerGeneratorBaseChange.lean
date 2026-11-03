module

public import PaperP1.Algebra.QuadraticTowerSumBaseChange

/-! # Every actual radical generator and every normal basis element commutes with base change -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerGeneratorBaseChange

open PaperP1.FiniteQuadraticTower PaperP1.QuadraticTowerBaseChange
  PaperP1.QuadraticTowerSumBaseChange QuadraticAlgebra

def indexEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    (s : List R) → Index s ≃ Index (s.map φ)
  | [] => Equiv.refl PUnit
  | _a :: s => (indexEquiv φ s).prodCongr (Equiv.refl (Fin 2))

theorem map_root {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : List R) (i : Fin s.length) :
    (mapData φ s).hom (root R s i) =
      root S (s.map φ) ⟨i.val, by simpa only [List.length_map] using i.isLt⟩ := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change quadraticMap (mapData φ s).hom _ _ ((mapData φ s).commutes a) omega = root S (φ a :: s.map φ) 0
      rw [quadraticMap_omega, root_zero]
    · change quadraticMap (mapData φ s).hom _ _ ((mapData φ s).commutes a)
        (algebraMap (Tower R s) (Tower R (a :: s)) (root R s j)) =
          root S (φ a :: s.map φ) (Fin.succ ⟨j.val, by simpa only [List.length_map] using j.isLt⟩)
      rw [quadraticMap_base, root_succ, ih j]

theorem map_basis {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (s : List R) (i : Index s) :
    (mapData φ s).hom (basis R s i) = basis S (s.map φ) (indexEquiv φ s i) := by
  induction s with
  | nil =>
    change PUnit at i
    change φ ((Module.Basis.singleton PUnit R) i) = (Module.Basis.singleton PUnit S) i
    exact (congrArg φ (Module.Basis.singleton_apply PUnit R i)).trans
      ((map_one φ).trans (Module.Basis.singleton_apply PUnit S i).symm)
  | cons a s ih =>
    obtain ⟨i, j⟩ := i
    fin_cases j
    · change (mapData φ (a :: s)).hom (basis R (a :: s) (i, 0)) =
        basis S (φ a :: s.map φ) (indexEquiv φ s i, 0)
      rw [basis_cons_zero, basis_cons_zero]
      change quadraticMap (mapData φ s).hom _ _ ((mapData φ s).commutes a)
        (algebraMap (Tower R s) (Tower R (a :: s)) (basis R s i)) = _
      rw [quadraticMap_base, ih i]
    · change (mapData φ (a :: s)).hom (basis R (a :: s) (i, 1)) =
        basis S (φ a :: s.map φ) (indexEquiv φ s i, 1)
      rw [basis_cons_one, basis_cons_one, map_mul, root_zero, root_zero]
      change quadraticMap (mapData φ s).hom _ _ ((mapData φ s).commutes a)
        (algebraMap (Tower R s) (Tower R (a :: s)) (basis R s i)) *
          quadraticMap (mapData φ s).hom _ _ ((mapData φ s).commutes a) omega = _
      rw [quadraticMap_base, quadraticMap_omega, ih i]

end PaperP1.QuadraticTowerGeneratorBaseChange
