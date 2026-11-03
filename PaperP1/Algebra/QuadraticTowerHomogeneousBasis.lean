module

public import PaperP1.Algebra.FiniteQuadraticTower
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-! # Every actual normal basis vector has its literal homogeneous radical degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerHomogeneousBasis

open Module PaperP1.FiniteQuadraticTower

def indexWeight {R : Type*} : (s : List R) → Index s → ℕ
  | [], _ => 0
  | _a :: s, (i, j) => indexWeight s i + j.val

theorem indexWeight_le_length {R : Type*} (s : List R) (i : Index s) : indexWeight s i ≤ s.length := by
  induction s with
  | nil => exact Nat.le_refl 0
  | cons a s ih =>
    obtain ⟨i, j⟩ := i
    have hj := j.isLt
    have hi := ih i
    change indexWeight s i + j.val ≤ s.length + 1
    omega

theorem basis_mem {R F A : Type*} [CommRing R] [CommRing F] [CommRing A] [Algebra F A]
    (G : ℕ → Submodule F A) [SetLike.GradedMonoid G] (D : ℕ)
    (s : List R) (g : Tower R s →+* A) (hroot : ∀ i, g (root R s i) ∈ G D) (i : Index s) :
    g (basis R s i) ∈ G (D * indexWeight s i) := by
  induction s with
  | nil =>
    change PUnit at i
    change g ((Basis.singleton PUnit R) i) ∈ G (D * 0)
    rw [Basis.singleton_apply, map_one, Nat.mul_zero]
    exact SetLike.one_mem_graded G
  | cons a s ih =>
    obtain ⟨i, j⟩ := i
    let gtail : Tower R s →+* A := g.comp (algebraMap (Tower R s) (Tower R (a :: s)))
    have htail : ∀ k, gtail (root R s k) ∈ G D := fun k ↦ hroot k.succ
    have hi := ih gtail htail i
    fin_cases j
    · change g (basis R (a :: s) (i, 0)) ∈ G (D * (indexWeight s i + 0))
      rw [basis_cons_zero]
      change gtail (basis R s i) ∈ G (D * (indexWeight s i + 0))
      simpa only [add_zero] using hi
    · change g (basis R (a :: s) (i, 1)) ∈ G (D * (indexWeight s i + 1))
      rw [basis_cons_one, map_mul]
      change gtail (basis R s i) * g (root R (a :: s) 0) ∈ G (D * (indexWeight s i + 1))
      rw [Nat.mul_add, Nat.mul_one]
      exact SetLike.mul_mem_graded hi (hroot 0)

end PaperP1.QuadraticTowerHomogeneousBasis
