module

public import PaperP1.Algebra.FiniteEvaluationAnnihilator
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.Data.Rat.Cast.Defs

/-! # Nonzero integral coefficient vectors for singular integer evaluation families -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegralEvaluationAnnihilator

open Finset Matrix

theorem coefficients {ι κ : Type*} [Fintype κ] [DecidableEq κ] (rows : ι → κ → ℤ)
    (hdet : ∀ f : κ → ι, Function.Injective f → Matrix.det (fun i j ↦ rows (f i) j) = 0) :
    ∃ w : κ → ℤ, w ≠ 0 ∧ ∀ i, ∑ j, rows i j * w j = 0 := by
  classical
  have hdetQ (f : κ → ι) (hf : Function.Injective f) :
      Matrix.det (fun i j ↦ (rows (f i) j : ℚ)) = 0 := by
    let A : Matrix κ κ ℤ := fun i j ↦ rows (f i) j
    have hA : A.det = 0 := hdet f hf
    change Matrix.det ((Int.castRingHom ℚ).mapMatrix A) = 0
    rw [← RingHom.map_det, hA, map_zero]
  obtain ⟨w, hw, he⟩ := FiniteEvaluationAnnihilator.coefficients (fun i j ↦ (rows i j : ℚ)) hdetQ
  obtain ⟨⟨b, hb⟩, hden⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors ℤ) (univ.image w)
  choose z hz using hden
  let u : κ → ℤ := fun j ↦ z (w j) (mem_image.mpr ⟨j, mem_univ j, rfl⟩)
  have hu (j : κ) : (u j : ℚ) = (b : ℚ) * w j := by
    exact hz (w j) (mem_image.mpr ⟨j, mem_univ j, rfl⟩)
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast (nonZeroDivisors.ne_zero hb)
  refine ⟨u, ?_, ?_⟩
  · intro hu0
    apply hw
    funext j
    have hj := hu j
    rw [hu0, Pi.zero_apply, Int.cast_zero] at hj
    exact (mul_eq_zero.mp hj.symm).resolve_left hbQ
  · intro i
    have hsum : (((∑ j, rows i j * u j) : ℤ) : ℚ) = 0 := by
      push_cast
      simp_rw [hu]
      calc
        _ = (b : ℚ) * ∑ j, (rows i j : ℚ) * w j := by
          rw [mul_sum]
          apply sum_congr rfl
          intro j _
          ring
        _ = 0 := by rw [he i, mul_zero]
    exact_mod_cast hsum

end PaperP1.IntegralEvaluationAnnihilator
