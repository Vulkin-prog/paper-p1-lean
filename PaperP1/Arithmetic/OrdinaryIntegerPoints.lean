module

public import PaperP1.Algebra.HomogeneousSplitRadicalRelations
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Ideal.Maps

/-! # Actual bounded integral points of an ordinary homogeneous quotient and their integer hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryIntegerPoints

open Finset MvPolynomial PaperP1.HomogeneousSplitRadicalRelations

variable {ι : Type*}

abbrev Point (ι : Type*) := Fin 3 ⊕ ι → ℤ

def evaluation (v : Point ι) : WeightedPolynomial ℚ ι →ₐ[ℚ] ℚ :=
  aeval (fun i ↦ (v i : ℚ))

theorem evaluation_X (v : Point ι) (i : Fin 3 ⊕ ι) : evaluation v (X i) = (v i : ℚ) := aeval_X _ _

def host (v : Point ι) : ℤ × ℤ := (v (Sum.inl 1), v (Sum.inl 0))

def lift (x y : ℤ) (w : ι → ℤ) : Point ι := Sum.elim ![y, x, 1] w

theorem host_lift (x y : ℤ) (w : ι → ℤ) : host (lift x y w) = (x, y) := rfl

theorem lift_Z (x y : ℤ) (w : ι → ℤ) : lift x y w (Sum.inl 2) = 1 := rfl

variable [Fintype ι] [DecidableEq ι]

def box (H : ℕ) : Finset (Point ι) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin 3 ⊕ ι ↦ Icc (-(H : ℤ)) H)).filter
    (fun v ↦ v (Sum.inl 2) = 1)

theorem mem_box (H : ℕ) (v : Point ι) :
    v ∈ box H ↔ (∀ i, |v i| ≤ (H : ℤ)) ∧ v (Sum.inl 2) = 1 := by
  classical
  simp only [box, mem_filter, Fintype.mem_piFinset, mem_Icc, abs_le]

def curvePoints (Q : Ideal (WeightedPolynomial ℚ ι)) (H : ℕ) : Finset (Point ι) := by
  classical
  exact (box H).filter (fun v ↦ Q ≤ RingHom.ker (evaluation v).toRingHom)

theorem mem_curvePoints (Q : Ideal (WeightedPolynomial ℚ ι)) (H : ℕ) (v : Point ι) :
    v ∈ curvePoints Q H ↔ ((∀ i, |v i| ≤ (H : ℤ)) ∧ v (Sum.inl 2) = 1) ∧
      Q ≤ RingHom.ker (evaluation v).toRingHom := by
  classical
  simp only [curvePoints, mem_filter, mem_box]

theorem hosts_card_le (Q : Ideal (WeightedPolynomial ℚ ι)) (H : ℕ) :
    ((curvePoints Q H).image host).card ≤ (curvePoints Q H).card := card_image_le

theorem lift_card_le (A : Finset (ℤ × ℤ)) (w : (ℤ × ℤ) → ι → ℤ)
    (Q : Ideal (WeightedPolynomial ℚ ι)) (H : ℕ)
    (hmem : ∀ p ∈ A, lift p.1 p.2 (w p) ∈ curvePoints Q H) :
    A.card ≤ (curvePoints Q H).card := by
  classical
  apply card_le_card_of_injOn (fun p : ℤ × ℤ ↦ lift p.1 p.2 (w p)) hmem
  intro p _hp q _hq hpq
  have h := congrArg host hpq
  simpa only [host_lift] using h

end PaperP1.OrdinaryIntegerPoints
