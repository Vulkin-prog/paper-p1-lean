module

public import PaperP1.Arithmetic.BranchShiftReductionCertificate
public import Mathlib.Tactic.Ring

/-! # The literal branch-collision and projected-model certificates combine with a uniform polynomial-height bound -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.BranchModelReductionCertificate
open PaperP1.BranchShiftReductionCertificate

theorem branch_bound (M A : ℕ) (hA : 0 < A) (S : Finset ℤ) (hcard : S.card ≤ M)
    (hheight : ∀ a ∈ S, |a| ≤ (A : ℤ)) :
    (certificate S).natAbs ≤ (2 * 2 ^ (M*(M-1))) * A ^ (M*(M-1)) := by
  have he : S.card*(S.card-1) ≤ M*(M-1) :=
    Nat.mul_le_mul hcard (Nat.sub_le_sub_right hcard 1)
  calc
    (certificate S).natAbs ≤ 2 * (2*A) ^ (S.card*(S.card-1)) := natAbs_bound S A hheight
    _ ≤ 2 * (2*A) ^ (M*(M-1)) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by omega : 0 < 2*A) he)
    _ = (2 * 2 ^ (M*(M-1))) * A ^ (M*(M-1)) := by rw [mul_pow]; ring

theorem combine (M T N A : ℕ) (hA : 0 < A) (S : Finset ℤ) (hcard : S.card ≤ M)
    (hheight : ∀ a ∈ S, |a| ≤ (A : ℤ)) (B₀ : ℤ) (hB₀ : B₀ ≠ 0) (hbound : B₀.natAbs ≤ T*A^N) :
    ∃ B : ℤ, B ≠ 0 ∧ B.natAbs ≤ (T * (2 * 2 ^ (M*(M-1)))) * A ^ (N+M*(M-1)) ∧
      ∀ p : ℕ, ¬ (p : ℤ) ∣ B → ¬ (p : ℤ) ∣ B₀ ∧ ¬ (p : ℤ) ∣ certificate S := by
  refine ⟨B₀ * certificate S, mul_ne_zero hB₀ (nonzero S), ?_, ?_⟩
  · rw [Int.natAbs_mul]
    calc
      B₀.natAbs * (certificate S).natAbs ≤ (T*A^N) * ((2 * 2 ^ (M*(M-1))) * A ^ (M*(M-1))) :=
        Nat.mul_le_mul hbound (branch_bound M A hA S hcard hheight)
      _ = (T * (2 * 2 ^ (M*(M-1)))) * A ^ (N+M*(M-1)) := by rw [pow_add]; ring
  · intro p hp
    exact ⟨fun hh ↦ hp (dvd_mul_of_dvd_left hh _), fun hh ↦ hp (dvd_mul_of_dvd_right hh _)⟩

end PaperP1.BranchModelReductionCertificate
