module

public import PaperP1.Algebra.BiquadraticNormModel
public import Mathlib.RingTheory.AlgebraTower

/-! # A literal finite quadratic tower with its free basis and actual radical generators -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace PaperP1.FiniteQuadraticTower

open Module

structure Stage (R : Type u) [CommRing R] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra R carrier]

attribute [instance] Stage.commRing Stage.algebra

@[reducible] def stage (R : Type u) [CommRing R] : List R → Stage R
  | [] => {
      carrier := R
      commRing := inferInstance
      algebra := inferInstance }
  | a :: s => {
      carrier := QuadraticAlgebra (stage R s).carrier (algebraMap R (stage R s).carrier a) 0
      commRing := inferInstance
      algebra := inferInstance }

abbrev Tower (R : Type u) [CommRing R] (s : List R) := (stage R s).carrier

def Index {R : Type u} : List R → Type
  | [] => PUnit
  | _ :: s => Index s × Fin 2

instance indexFintype {R : Type u} (s : List R) : Fintype (Index s) := by
  induction s with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons a s ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Index s × Fin 2))

def basis (R : Type u) [CommRing R] : (s : List R) → Basis (Index s) R (Tower R s)
  | [] => Basis.singleton PUnit R
  | a :: s => (basis R s).smulTower (QuadraticAlgebra.basis (algebraMap R (Tower R s) a) 0)

instance towerFree (R : Type u) [CommRing R] (s : List R) : Module.Free R (Tower R s) := .of_basis (basis R s)
instance towerFinite (R : Type u) [CommRing R] (s : List R) : Module.Finite R (Tower R s) := .of_basis (basis R s)

theorem base_injective (R : Type u) [CommRing R] (s : List R) :
    Function.Injective (algebraMap R (Tower R s)) := by
  induction s with
  | nil => exact fun _ _ h ↦ h
  | cons a s ih => exact QuadraticAlgebra.algebraMap_injective.comp ih

instance towerCharZero (R : Type u) [CommRing R] [CharZero R] (s : List R) : CharZero (Tower R s) :=
  charZero_of_injective_algebraMap (base_injective R s)

theorem index_card {R : Type u} (s : List R) : Fintype.card (Index s) = 2 ^ s.length := by
  rw [Fintype.card_eq_nat_card]
  induction s with
  | nil =>
    change Nat.card PUnit = 1
    simp
  | cons a s ih =>
    change Nat.card (Index s × Fin 2) = 2 ^ (s.length + 1)
    rw [Nat.card_prod, Nat.card_fin, ih, pow_succ]

theorem finrank (R : Type u) [CommRing R] [Nontrivial R] (s : List R) :
    Module.finrank R (Tower R s) = 2 ^ s.length := by
  rw [Module.finrank_eq_card_basis (basis R s), index_card]

def root (R : Type u) [CommRing R] : (s : List R) → Fin s.length → Tower R s
  | [], i => Fin.elim0 i
  | a :: s, i => Fin.cases QuadraticAlgebra.omega
      (fun j ↦ algebraMap (Tower R s) (Tower R (a :: s)) (root R s j)) i

theorem root_zero (R : Type u) [CommRing R] (a : R) (s : List R) :
    root R (a :: s) 0 = QuadraticAlgebra.omega := rfl

theorem root_succ (R : Type u) [CommRing R] (a : R) (s : List R) (i : Fin s.length) :
    root R (a :: s) i.succ = algebraMap (Tower R s) (Tower R (a :: s)) (root R s i) := rfl

theorem root_square (R : Type u) [CommRing R] (s : List R) (i : Fin s.length) :
    root R s i ^ 2 = algebraMap R (Tower R s) (s.get i) := by
  induction s with
  | nil => exact Fin.elim0 i
  | cons a s ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [root_zero, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
      rfl
    · rw [root_succ, ← map_pow, ih j]
      rfl

theorem basis_cons_zero (R : Type u) [CommRing R] (a : R) (s : List R) (i : Index s) :
    basis R (a :: s) (i, 0) = algebraMap (Tower R s) (Tower R (a :: s)) (basis R s i) := by
  change ((basis R s).smulTower (QuadraticAlgebra.basis (algebraMap R (Tower R s) a) 0)) (i, 0) = _
  rw [Basis.smulTower_apply, QuadraticAlgebra.basis_apply_zero, Algebra.smul_def, mul_one]

theorem basis_cons_one (R : Type u) [CommRing R] (a : R) (s : List R) (i : Index s) :
    basis R (a :: s) (i, 1) = algebraMap (Tower R s) (Tower R (a :: s)) (basis R s i) * root R (a :: s) 0 := by
  change ((basis R s).smulTower (QuadraticAlgebra.basis (algebraMap R (Tower R s) a) 0)) (i, 1) = _
  rw [Basis.smulTower_apply, QuadraticAlgebra.basis_apply_one, Algebra.smul_def, root_zero]

theorem induction_on (R : Type u) [CommRing R] (s : List R) :
    ∀ P : Tower R s → Prop, (∀ r, P (algebraMap R (Tower R s) r)) →
      (∀ i, P (root R s i)) → (∀ x y, P x → P y → P (x + y)) →
      (∀ x y, P x → P y → P (x * y)) → ∀ x, P x := by
  induction s with
  | nil =>
    intro P hbase _hroot _hadd _hmul x
    exact hbase x
  | cons a s ih =>
    intro P hbase hroot hadd hmul x
    have hold : ∀ z : Tower R s, P (algebraMap (Tower R s) (Tower R (a :: s)) z) := by
      apply ih
      · intro r
        exact hbase r
      · intro i
        exact hroot i.succ
      · intro z w hz hw
        simpa only [map_add] using hadd _ _ hz hw
      · intro z w hz hw
        simpa only [map_mul] using hmul _ _ hz hw
    have hω := hroot 0
    have hrep : algebraMap (Tower R s) (Tower R (a :: s)) x.re +
        algebraMap (Tower R s) (Tower R (a :: s)) x.im * root R (a :: s) 0 = x := by
      rw [root_zero]
      simpa only [Algebra.smul_def, mul_one] using QuadraticAlgebra.re_smul_add_im_smul x
    rw [← hrep]
    exact hadd _ _ (hold x.re) (hmul _ _ (hold x.im) hω)

theorem adjoin_roots (R : Type u) [CommRing R] (s : List R) :
    Algebra.adjoin R (Set.range (root R s)) = ⊤ := by
  let A := Algebra.adjoin R (Set.range (root R s))
  apply Algebra.eq_top_iff.mpr
  exact induction_on R s (fun x ↦ x ∈ A) (fun r ↦ A.algebraMap_mem r)
    (fun i ↦ Algebra.subset_adjoin ⟨i, rfl⟩) (fun _ _ ↦ A.add_mem) (fun _ _ ↦ A.mul_mem)

end PaperP1.FiniteQuadraticTower
