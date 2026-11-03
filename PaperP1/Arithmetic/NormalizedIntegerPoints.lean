module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps

/-! # Actual bounded integer points in an arbitrary normalized projective coordinate chart -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NormalizedIntegerPoints

variable {σ : Type}

def evaluation (v : σ → ℤ) : MvPolynomial σ ℚ →ₐ[ℚ] ℚ := MvPolynomial.aeval fun i ↦ (v i : ℚ)

local instance indexFintype [Finite σ] : Fintype σ := Fintype.ofFinite σ

variable [Finite σ]

def box (z : σ) (H : ℕ) : Finset (σ → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ ↦ Finset.Icc (-(H : ℤ)) H).filter fun v ↦ v z = 1

def points (Q : Ideal (MvPolynomial σ ℚ)) (z : σ) (H : ℕ) : Finset (σ → ℤ) := by
  classical
  exact (box z H).filter fun v ↦ Q ≤ RingHom.ker (evaluation v).toRingHom

theorem mem_box (z : σ) (H : ℕ) (v : σ → ℤ) :
    v ∈ box z H ↔ (∀ i, |v i| ≤ (H : ℤ)) ∧ v z = 1 := by
  classical
  simp only [box, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le]

theorem mem_points (Q : Ideal (MvPolynomial σ ℚ)) (z : σ) (H : ℕ) (v : σ → ℤ) :
    v ∈ points Q z H ↔ ((∀ i, |v i| ≤ (H : ℤ)) ∧ v z = 1) ∧
      Q ≤ RingHom.ker (evaluation v).toRingHom := by
  classical
  simp only [points, Finset.mem_filter, mem_box]

end PaperP1.NormalizedIntegerPoints
