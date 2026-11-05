module

public import PaperP1.Arithmetic.DegreeUniformAffineParameters

/-! # An absolute polynomial-degree prime scale for the affine determinant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeUniformPrimeScale

open DegreeUniformAffineParameters

theorem box_root_bound (D N : ℕ) (hD : 2 ≤ D) :
    (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤
      2 * D * (N : ℝ) ^ (1 / (D : ℝ)) := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hroot : ((D : ℝ) + 1) ^ (1 / (D : ℝ)) ≤ (D : ℝ) + 1 :=
    Real.rpow_le_self_of_one_le (by linarith) ((div_le_one hDpos).mpr hD1)
  push_cast
  rw [Real.mul_rpow (by positivity) hN0]
  exact mul_le_mul_of_nonneg_right (hroot.trans (by linarith))
    (Real.rpow_nonneg hN0 _)

theorem exists_scale (P₀ : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ D N : ℕ, 2 ≤ D → D ≤ N →
      ∃ P : ℕ, P₀ ≤ P ∧ avoidanceCount D N ^ 2 ≤ P ∧
        3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ)) ≤ P ∧
        (P : ℝ) ≤ K * (D : ℝ) ^ 6 * (logarithmicBudget N : ℝ) ^ 2 *
          (N : ℝ) ^ (1 / (D : ℝ)) := by
  let K : ℝ := 16385 + 6 * Real.exp 1 + P₀
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro D N hD hDN
  let L := logarithmicBudget N
  let m := avoidanceCount D N
  let R := (N : ℝ) ^ (1 / (D : ℝ))
  let V := 3 * Real.exp 1 * (((D + 1) * N : ℕ) : ℝ) ^ (1 / (D : ℝ))
  let P := ⌈V⌉₊ + P₀ + m ^ 2
  have hN : 1 ≤ N := by omega
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hL1 : (1 : ℝ) ≤ L := by
    exact_mod_cast (show 1 ≤ logarithmicBudget N by unfold logarithmicBudget; omega)
  have hR1 : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hpoly1 : (1 : ℝ) ≤ (D : ℝ) ^ 6 * (L : ℝ) ^ 2 := by
    have hd : (1 : ℝ) ≤ (D : ℝ) ^ 6 := one_le_pow₀ hD1
    have hl : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    nlinarith only [hd, hl, mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hl)]
  have hDpoly : (D : ℝ) ≤ (D : ℝ) ^ 6 * (L : ℝ) ^ 2 := by
    calc
      _ ≤ (D : ℝ) ^ 6 := le_self_pow₀ hD1 (by decide : 6 ≠ 0)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hL1)
  have hpolyR : (D : ℝ) ^ 6 * (L : ℝ) ^ 2 ≤ (D : ℝ) ^ 6 * (L : ℝ) ^ 2 * R :=
    le_mul_of_one_le_right (by positivity) hR1
  have hunit : (1 : ℝ) ≤ (D : ℝ) ^ 6 * (L : ℝ) ^ 2 * R := hpoly1.trans hpolyR
  have hV : V ≤ 6 * Real.exp 1 * D * R := by
    have hh := mul_le_mul_of_nonneg_left (box_root_bound D N hD)
      (by positivity : (0 : ℝ) ≤ 3 * Real.exp 1)
    dsimp only [V, R]
    nlinarith only [hh]
  have hceil : (⌈V⌉₊ : ℝ) ≤ 6 * Real.exp 1 * D * R + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ V by dsimp [V]; positivity)).le.trans (by linarith only [hV])
  have hm : (m : ℝ) ≤ 128 * (D : ℝ) ^ 3 * L := by
    exact_mod_cast avoidance_le D N hD
  have hmsq : (m : ℝ) ^ 2 ≤ 16384 * ((D : ℝ) ^ 6 * (L : ℝ) ^ 2) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg m) hm 2
    nlinarith only [hh]
  refine ⟨P, by dsimp [P]; omega, by change m ^ 2 ≤ ⌈V⌉₊ + P₀ + m ^ 2; omega,
    (Nat.le_ceil V).trans ?_, ?_⟩
  · exact_mod_cast (show ⌈V⌉₊ ≤ P by dsimp [P]; omega)
  · have hmain : 6 * Real.exp 1 * D * R ≤
        6 * Real.exp 1 * ((D : ℝ) ^ 6 * (L : ℝ) ^ 2 * R) :=
      calc
        _ = (6 * Real.exp 1) * ((D : ℝ) * R) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hDpoly (show 0 ≤ R by positivity)) (by positivity)
    have hmterm : (m : ℝ) ^ 2 ≤ 16384 * ((D : ℝ) ^ 6 * (L : ℝ) ^ 2 * R) :=
      hmsq.trans (mul_le_mul_of_nonneg_left hpolyR (by norm_num))
    have hconst := mul_le_mul_of_nonneg_left hunit (Nat.cast_nonneg (α := ℝ) P₀)
    have hP : (P : ℝ) = (⌈V⌉₊ : ℝ) + P₀ + (m : ℝ) ^ 2 := by dsimp [P]; push_cast; rfl
    dsimp only [K, L, R] at *
    rw [hP]
    nlinarith only [hceil, hmain, hmterm, hconst, hunit]

end PaperP1.DegreeUniformPrimeScale
