module

public import PaperP1.Arithmetic.ExactMatchCongruences

/-! # Reduction of an actual affine integer relation preserves height bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReducedAffineData

theorem reduce {C D t z : ℕ} {h : ℤ} (hC : 0 < C) (hD : 0 < D)
    (heq : (D : ℤ) * z = (C : ℤ) * t + h) :
    ∃ c d : ℕ, ∃ h' : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ c ≤ C ∧ d ≤ D ∧
      |h'| ≤ |h| ∧ (d : ℤ) * z = (c : ℤ) * t + h' := by
  let g : ℕ := Nat.gcd C D
  let c : ℕ := C / g
  let d : ℕ := D / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left D hC
  have hc : 0 < c := Nat.div_pos (Nat.gcd_le_left D hC) hg
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_right C hD) hg
  have hcop : c.Coprime d := Nat.coprime_div_gcd_div_gcd hg
  have hCeq : g * c = C := Nat.mul_div_cancel' (Nat.gcd_dvd_left C D)
  have hDeq : g * d = D := Nat.mul_div_cancel' (Nat.gcd_dvd_right C D)
  have hCeqZ : (g : ℤ) * c = C := by exact_mod_cast hCeq
  have hDeqZ : (g : ℤ) * d = D := by exact_mod_cast hDeq
  have hCdiv : (g : ℤ) ∣ (C : ℤ) := by exact_mod_cast Nat.gcd_dvd_left C D
  have hDdiv : (g : ℤ) ∣ (D : ℤ) := by exact_mod_cast Nat.gcd_dvd_right C D
  have hhval : h = (D : ℤ) * z - (C : ℤ) * t := by linarith only [heq]
  have hdiv : (g : ℤ) ∣ h := by
    rw [hhval]
    exact dvd_sub (dvd_mul_of_dvd_left hDdiv (z : ℤ)) (dvd_mul_of_dvd_left hCdiv (t : ℤ))
  obtain ⟨h', hh'⟩ := hdiv
  have hg1 : (1 : ℤ) ≤ g := by exact_mod_cast (show 1 ≤ g by omega)
  have hhle : |h'| ≤ |h| := by
    rw [hh', abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) g)]
    have hmul := mul_le_mul_of_nonneg_right hg1 (abs_nonneg h')
    simpa only [one_mul] using hmul
  have hcancel : (g : ℤ) * ((d : ℤ) * z) = (g : ℤ) * ((c : ℤ) * t + h') := by
    calc
      _ = (D : ℤ) * z := by rw [← mul_assoc, hDeqZ]
      _ = (C : ℤ) * t + h := heq
      _ = _ := by rw [← hCeqZ, hh']; ring
  refine ⟨c, d, h', hc, hd, hcop, Nat.div_le_self _ _, Nat.div_le_self _ _, hhle, ?_⟩
  exact mul_left_cancel₀ (by exact_mod_cast hg.ne' : (g : ℤ) ≠ 0) hcancel

end PaperP1.ReducedAffineData
