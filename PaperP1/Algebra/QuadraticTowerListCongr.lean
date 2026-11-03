module

public import PaperP1.Algebra.FiniteQuadraticTower

/-! # Literal transport of a radical tower along equality of the actual equation lists -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticTowerListCongr

open PaperP1.FiniteQuadraticTower

def congr (R : Type*) [CommRing R] {s t : List R} (h : s = t) : Tower R s ≃ₐ[R] Tower R t :=
  h ▸ AlgEquiv.refl

theorem congr_base (R : Type*) [CommRing R] {s t : List R} (h : s = t) (r : R) :
    congr R h (algebraMap R (Tower R s) r) = algebraMap R (Tower R t) r :=
  (congr R h).commutes r

theorem congr_root (R : Type*) [CommRing R] {s t : List R} (h : s = t) (i : Fin s.length) :
    congr R h (root R s i) = root R t ⟨i.val, by rw [← h]; exact i.isLt⟩ := by
  subst t
  rfl

theorem congr_basis (R : Type*) [CommRing R] {s t : List R} (h : s = t) (i : Index s) :
    congr R h (basis R s i) = basis R t (h ▸ i) := by
  subst t
  rfl

end PaperP1.QuadraticTowerListCongr
