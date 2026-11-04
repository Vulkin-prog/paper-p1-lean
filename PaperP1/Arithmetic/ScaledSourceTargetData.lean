module

public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # Scaled centre alignment yields polynomial-height actual affine target data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledSourceTargetData

open PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount

theorem bounded {q b d D x z t L r s : ℕ} (hq : 0 < q) (hb : 0 < b) (hd : 0 < d)
    (hx : 0 < x) (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = q * t)
    (hr : 0 < r) (hs : 0 < s) (hrB : r ≤ (L + 1) ^ 3) (hsB : s ≤ (L + 1) ^ 3)
    (hwidth : 2 * (D + b) ≤ L + 1) (hdB : d ≤ (L + 1) ^ 2)
    (halign : |(r : ℤ) * (d * z : ℕ) - (s : ℤ) * (b * x : ℕ)| ≤
      ((r + s : ℕ) : ℤ) * ((D * (L + 1) : ℕ) : ℤ)) :
    ∃ c e : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < e ∧ c.Coprime e ∧ e ≤ (L + 1) ^ 5 ∧
      |h| ≤ ((L + 1) ^ 5 : ℕ) ∧ (e : ℤ) * z = (c : ℤ) * t + h := by
  have hoff : |(x : ℤ) - (q * t : ℕ)| ≤ ((L + 1 : ℕ) : ℤ) := by
    have heq : (x : ℤ) + offset i = (q * t : ℕ) := by
      rw [← label_cast hx]
      exact_mod_cast hbase
    have ho := EnlargedPairGeometry.offset_abs i
    have hid : (x : ℤ) - (q * t : ℕ) = -offset i := by linarith only [heq]
    simpa only [hid, abs_neg] using ho
  let C := s * b * q
  let E := r * d
  let hraw : ℤ := (E : ℤ) * z - (C : ℤ) * t
  have heq : hraw = ((r : ℤ) * (d * z : ℕ) - (s : ℤ) * (b * x : ℕ)) +
      ((s * b : ℕ) : ℤ) * ((x : ℤ) - (q * t : ℕ)) := by
    dsimp only [hraw, C, E]
    push_cast
    ring
  have hrawBound : |hraw| ≤ (((r + s) * ((D + b) * (L + 1)) : ℕ) : ℤ) := by
    rw [heq]
    calc
      _ ≤ |(r : ℤ) * (d * z : ℕ) - (s : ℤ) * (b * x : ℕ)| +
          |((s * b : ℕ) : ℤ) * ((x : ℤ) - (q * t : ℕ))| := abs_add_le _ _
      _ ≤ ((r + s : ℕ) : ℤ) * ((D * (L + 1) : ℕ) : ℤ) + ((s * b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) (s * b))]
        exact add_le_add halign (mul_le_mul_of_nonneg_left hoff (Nat.cast_nonneg _))
      _ ≤ _ := by
        push_cast
        have hnn : (0 : ℤ) ≤ (r : ℤ) * b * ((L : ℤ) + 1) := by positivity
        nlinarith only [hnn]
  have hsum : r + s ≤ 2 * (L + 1) ^ 3 := by omega
  have hmul := Nat.mul_le_mul_right ((D + b) * (L + 1)) hsum
  have hwidthMul := Nat.mul_le_mul_right ((L + 1) ^ 4) hwidth
  have hheight : (r + s) * ((D + b) * (L + 1)) ≤ (L + 1) ^ 5 := by
    have h4 : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
    have h5 : (L + 1) * (L + 1) ^ 4 = (L + 1) ^ 5 := by ring
    nlinarith only [hmul, hwidthMul, h4, h5]
  have hEheight : E ≤ (L + 1) ^ 5 := by
    calc
      _ ≤ (L + 1) ^ 3 * (L + 1) ^ 2 := Nat.mul_le_mul hrB hdB
      _ = _ := by ring
  obtain ⟨c, e, h, hc, he, hcop, _hcC, heE, hh, htarget⟩ := ReducedAffineData.reduce
    (Nat.mul_pos (Nat.mul_pos hs hb) hq) (Nat.mul_pos hr hd)
    (show (E : ℤ) * z = (C : ℤ) * t + hraw by dsimp [hraw]; ring)
  exact ⟨c, e, h, hc, he, hcop, heE.trans hEheight,
    hh.trans (hrawBound.trans (by exact_mod_cast hheight)), htarget⟩

end PaperP1.ScaledSourceTargetData
