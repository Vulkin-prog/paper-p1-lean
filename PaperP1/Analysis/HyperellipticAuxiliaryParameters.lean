module

public import PaperP1.Analysis.SquareRootPointErrorThreshold

/-! # Uniform numerical multiplicity and prime choices for the actual quadratic-curve estimate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HyperellipticAuxiliaryParameters

theorem exists_parameters (g : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ m K : ℕ, g + 1 ≤ m ∧ 3 ≤ K ∧ m ≤ K ∧ 2 * g + 2 ≤ K ∧
      g + m * (m + g) + m * (m - 1) * ((2 * g + 1) - 2) + 1 ≤ K ∧
      ((g + 1 : ℕ) : ℝ) ≤ (η / 2) * m ∧
      ∀ p : ℕ, K ≤ p → ((2 * g + 1 : ℕ) : ℝ) ≤ (η / 2) * p := by
  have hhalf : (0 : ℝ) < η / 2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (((g + 1 : ℕ) : ℝ) / (η / 2))
  let m : ℕ := max (g + 1) n
  have hnm : (n : ℝ) ≤ m := by exact_mod_cast (Nat.le_max_right (g + 1) n)
  have hmx : ((g + 1 : ℕ) : ℝ) ≤ (η / 2) * m := by
    have hh := (div_lt_iff₀ hhalf).mp (lt_of_lt_of_le hn hnm)
    nlinarith only [hh]
  obtain ⟨k, hk⟩ := exists_nat_gt (((2 * g + 1 : ℕ) : ℝ) / (η / 2))
  let C : ℕ := g + m * (m + g) + m * (m - 1) * ((2 * g + 1) - 2) + 1
  let K : ℕ := max 3 (max m (max (2 * g + 2) (max C k)))
  refine ⟨m, K, Nat.le_max_left _ _, ?_, ?_, ?_, ?_, hmx, ?_⟩
  · dsimp only [K]
    omega
  · dsimp only [K]
    omega
  · dsimp only [K]
    omega
  · change C ≤ K
    dsimp only [K]
    omega
  · intro p hp
    have hkp : k ≤ p := by dsimp only [K] at hp; omega
    have hkpR : (k : ℝ) ≤ p := by exact_mod_cast hkp
    have hh := (div_lt_iff₀ hhalf).mp (lt_of_lt_of_le hk hkpR)
    nlinarith only [hh]

theorem point_upper_arithmetic (g m p : ℕ) (η : ℝ) (hm : 0 < m)
    (hsmall : ((g + 1 : ℕ) : ℝ) ≤ (η / 2) * m)
    (hlarge : ((2 * g + 1 : ℕ) : ℝ) ≤ (η / 2) * p) :
    (((p - 1) + p * (m + g) : ℕ) : ℝ) / m + ((2 * g + 1 : ℕ) : ℝ) ≤
      (1 + η) * p := by
  have hLNat : (p - 1) + p * (m + g) ≤ p * m + p * (g + 1) := by
    calc
      _ ≤ p + p * (m + g) := Nat.add_le_add_right (Nat.sub_le p 1) _
      _ = _ := by ring
  have hL : (((p - 1) + p * (m + g) : ℕ) : ℝ) ≤
      (p : ℝ) * m + p * ((g + 1 : ℕ) : ℝ) := by exact_mod_cast hLNat
  have hx := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hy := mul_le_mul_of_nonneg_left hlarge (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_iff_of_pos_right hmR).mp
  rw [add_mul, div_mul_cancel₀ _ hmR.ne']
  nlinarith only [hL, hx, hy]

end PaperP1.HyperellipticAuxiliaryParameters
