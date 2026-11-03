module

public import PaperP1.Algebra.FiniteQuadraticTower

/-! # The actual radical generators are distinct vectors of the explicit tower basis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerRootBasis

open Module PaperP1.FiniteQuadraticTower

def zeroIndex {R : Type*} : (s : List R) → Index s
  | [] => PUnit.unit
  | _ :: s => (zeroIndex s, 0)

def singleIndex {R : Type*} : (s : List R) → Fin s.length → Index s
  | [], i => Fin.elim0 i
  | _ :: s, i => Fin.cases (zeroIndex s, 1) (fun j ↦ (singleIndex s j, 0)) i

theorem basis_zero (R : Type*) [CommRing R] (s : List R) : basis R s (zeroIndex s) = 1 := by
  induction s with
  | nil => exact Basis.singleton_apply PUnit R _
  | cons a s ih =>
    change basis R (a :: s) (zeroIndex s, 0) = 1
    rw [basis_cons_zero, ih, map_one]

theorem singleIndex_injective {R : Type*} (s : List R) : Function.Injective (singleIndex s) := by
  induction s with
  | nil => intro i; exact Fin.elim0 i
  | cons a s ih =>
    intro i
    refine Fin.cases ?_ (fun i' ↦ ?_) i
    · intro j
      refine Fin.cases ?_ (fun j' ↦ ?_) j
      · intro _h; rfl
      · intro h
        have hh : (1 : Fin 2) = 0 := congrArg Prod.snd h
        norm_num at hh
    · intro j
      refine Fin.cases ?_ (fun j' ↦ ?_) j
      · intro h
        have hh : (0 : Fin 2) = 1 := congrArg Prod.snd h
        norm_num at hh
      · intro h
        exact congrArg Fin.succ (ih (congrArg Prod.fst h))

theorem basis_single (R : Type*) [CommRing R] (s : List R) :
    ∀ i : Fin s.length, basis R s (singleIndex s i) = root R s i := by
  induction s with
  | nil => intro i; exact Fin.elim0 i
  | cons a s ih =>
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · change basis R (a :: s) (zeroIndex s, 1) = root R (a :: s) 0
      rw [basis_cons_one, basis_zero, map_one, one_mul]
    · change basis R (a :: s) (singleIndex s j, 0) = root R (a :: s) j.succ
      rw [basis_cons_zero, ih, root_succ]

theorem roots_linearlyIndependent (R : Type*) [CommRing R] (s : List R) :
    LinearIndependent R (root R s) := by
  have hh := (basis R s).linearIndependent.comp (singleIndex s) (singleIndex_injective s)
  simpa only [Function.comp_def, basis_single] using hh

end PaperP1.QuadraticTowerRootBasis
