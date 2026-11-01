module

public import PaperP1.Arithmetic.ReducedAffineData
public import PaperP1.Arithmetic.EnlargedPairGeometry

/-! # Literal alignment of a target with the compressed source gives bounded affine data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedTargetAlignment

def Aligned (D X z L : ℕ) : Prop :=
  ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ r.Coprime s ∧ r ≤ (L + 1) ^ 3 ∧ s ≤ (L + 1) ^ 3 ∧
    |(r : ℤ) * z - (s : ℤ) * X| ≤ ((r + s : ℕ) : ℤ) * ((D * (L + 1) : ℕ) : ℤ)

theorem of_geometric {r s X z L : ℕ} (hr : 0 < r) (hs : 0 < s) (hcop : r.Coprime s)
    (hrB : r ≤ (L + 1) ^ 3) (hsB : s ≤ (L + 1) ^ 3)
    (hgeom : EnlargedPairGeometry.Geometric r s X z L) : Aligned 1 X z L := by
  refine ⟨r, s, hr, hs, hcop, hrB, hsB, ?_⟩
  simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hgeom

theorem bounded_data {D a b t z L : ℕ} (ha : 0 < a) (hb : 0 < b) (hD : 2 * D ≤ L + 1)
    (halign : Aligned D (a * b * t) z L) :
    ∃ c d : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ (L + 1) ^ 5 ∧
      |h| ≤ ((L + 1) ^ 5 : ℕ) ∧ (d : ℤ) * z = (c : ℤ) * t + h := by
  obtain ⟨r, s, hr, hs, _, hrB, hsB, hgeom⟩ := halign
  let C : ℕ := s * (a * b)
  let hraw : ℤ := (r : ℤ) * z - (s : ℤ) * (a * b * t : ℕ)
  have hC : 0 < C := Nat.mul_pos hs (Nat.mul_pos ha hb)
  have htarget : (r : ℤ) * z = (C : ℤ) * t + hraw := by dsimp [C, hraw]; ring
  have hBpos : 0 < L + 1 := by omega
  have hsum : r + s ≤ 2 * (L + 1) ^ 3 := by omega
  have hmul := Nat.mul_le_mul_right (D * (L + 1)) hsum
  have hDmul := Nat.mul_le_mul_right ((L + 1) ^ 4) hD
  have hbound : (r + s) * (D * (L + 1)) ≤ (L + 1) ^ 5 := by
    have hfour : (L + 1) ^ 3 * (L + 1) = (L + 1) ^ 4 := by ring
    have hfive : (L + 1) * (L + 1) ^ 4 = (L + 1) ^ 5 := by ring
    nlinarith only [hmul, hDmul, hfour, hfive]
  have hhraw : |hraw| ≤ ((L + 1) ^ 5 : ℕ) :=
    hgeom.trans (by exact_mod_cast hbound)
  obtain ⟨c, d, h, hc, hd, hcop, _, hdd, hhle, heq⟩ := ReducedAffineData.reduce hC hr htarget
  refine ⟨c, d, h, hc, hd, hcop, ?_, hhle.trans hhraw, heq⟩
  exact hdd.trans (hrB.trans (Nat.pow_le_pow_right hBpos (by norm_num : 3 ≤ 5)))

end PaperP1.CompressedTargetAlignment
