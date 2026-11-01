module

public import PaperP1.Arithmetic.IntervalResidueError
public import Mathlib.RingTheory.Coprime.Lemmas

/-! # Exact residue classes of an affine integer divisibility constraint -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.AffineResidueClasses

open Finset

def solutions (r d : ℕ) (h a b : ℤ) : Finset ℤ :=
  (Ico a b).filter fun k ↦ (r : ℤ) ∣ h + (d : ℤ) * k

theorem exists_solution {r d : ℕ} (hcop : d.Coprime r) (h : ℤ) :
    ∃ v : ℤ, (r : ℤ) ∣ h + (d : ℤ) * v := by
  have hI : IsCoprime (d : ℤ) (r : ℤ) := hcop.isCoprime
  obtain ⟨u, v, huv⟩ := hI
  refine ⟨-h * u, ⟨h * v, ?_⟩⟩
  have heq : 1 - u * (d : ℤ) = v * (r : ℤ) := by linarith
  calc
    h + (d : ℤ) * (-h * u) = h * (1 - u * (d : ℤ)) := by ring
    _ = h * (v * (r : ℤ)) := by rw [heq]
    _ = (r : ℤ) * (h * v) := by ring

theorem affine_iff_modEq {r d : ℕ} (hcop : d.Coprime r) (h v : ℤ)
    (hv : (r : ℤ) ∣ h + (d : ℤ) * v) (k : ℤ) :
    (r : ℤ) ∣ h + (d : ℤ) * k ↔ k ≡ v [ZMOD (r : ℤ)] := by
  constructor
  · intro hk
    have hsub := dvd_sub hk hv
    have heq : (h + (d : ℤ) * k) - (h + (d : ℤ) * v) = (d : ℤ) * (k - v) := by ring
    rw [heq] at hsub
    have hI : IsCoprime (r : ℤ) (d : ℤ) := hcop.symm.isCoprime
    have hdiv : (r : ℤ) ∣ k - v := hI.dvd_of_dvd_mul_left hsub
    exact (Int.modEq_iff_dvd.mpr hdiv).symm
  · intro hk
    have hdiv : (r : ℤ) ∣ k - v := Int.modEq_iff_dvd.mp hk.symm
    have hmul : (r : ℤ) ∣ (d : ℤ) * (k - v) := hdiv.mul_left (d : ℤ)
    have hadd := dvd_add hv hmul
    have heq : (h + (d : ℤ) * v) + (d : ℤ) * (k - v) = h + (d : ℤ) * k := by ring
    rwa [heq] at hadd

theorem solutions_eq_residue {r d : ℕ} (hcop : d.Coprime r) (h a b : ℤ) :
    ∃ v : ℤ, solutions r d h a b = {k ∈ Ico a b | k ≡ v [ZMOD (r : ℤ)]} := by
  obtain ⟨v, hv⟩ := exists_solution hcop h
  refine ⟨v, ?_⟩
  ext k
  simp only [solutions, mem_filter]
  exact and_congr_right (fun _ ↦ affine_iff_modEq hcop h v hv k)

theorem abs_error {r d : ℕ} (hr : 0 < r) (hcop : d.Coprime r) (h a b : ℤ) (hab : a ≤ b) :
    |((solutions r d h a b).card : ℚ) - ((b - a : ℤ) : ℚ) / r| ≤ 1 := by
  obtain ⟨v, hv⟩ := solutions_eq_residue hcop h a b
  rw [hv]
  simpa only [Int.cast_natCast] using IntervalResidueError.abs_error a b v r (by exact_mod_cast hr) hab

end PaperP1.AffineResidueClasses
