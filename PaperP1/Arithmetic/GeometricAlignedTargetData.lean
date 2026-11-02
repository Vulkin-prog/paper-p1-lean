module

public import PaperP1.Arithmetic.EnlargedSourceTargetGeometry

/-! # Bounded geometric target ratios produce reduced affine data at quadratic word height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricAlignedTargetData

open PaperP1.Model PaperP1.Affine PaperP1.NormalizedUnitCount

theorem scaled_offset_bound {a r s x z L t : ℕ} (hx : 0 < x)
    (hgeom : EnlargedPairGeometry.Geometric r s x z L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    |(r : ℤ) * z - (a * s : ℕ) * (t : ℤ)| ≤ ((r + 2 * s) * (L + 1) : ℕ) := by
  have hlabel := congrArg (fun n : ℕ ↦ (n : ℤ)) hbase
  rw [label_cast hx] at hlabel
  push_cast at hlabel
  have heq : (r : ℤ) * z - (a * s : ℕ) * (t : ℤ) =
      -((s : ℤ) * x - (r : ℤ) * z) - (s : ℤ) * offset i := by
    push_cast
    have hh := congrArg (fun w : ℤ ↦ (s : ℤ) * w) hlabel
    nlinarith only [hh]
  rw [heq]
  calc
    _ ≤ |-((s : ℤ) * x - (r : ℤ) * z)| + |(s : ℤ) * offset i| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (-((s : ℤ) * x - (r : ℤ) * z)) (-((s : ℤ) * offset i))
    _ = |(s : ℤ) * x - (r : ℤ) * z| + (s : ℤ) * |offset i| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) s)]
    _ ≤ ((r + s : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) + (s : ℤ) * ((L + 1 : ℕ) : ℤ) :=
      add_le_add hgeom (mul_le_mul_of_nonneg_left (EnlargedPairGeometry.offset_abs i) (Nat.cast_nonneg s))
    _ = _ := by push_cast; ring

theorem reduced_affine_data {a r s x z L t : ℕ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (hx : 0 < x) (hgeom : EnlargedPairGeometry.Geometric r s x z L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ r ∧
      |(d : ℤ) * z - (c : ℤ) * t| ≤ ((r + 2 * s) * (L + 1) : ℕ) := by
  let g := Nat.gcd (a * s) r
  let c := (a * s) / g
  let d := r / g
  have has : 0 < a * s := Nat.mul_pos ha hs
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r has
  have hc : 0 < c := Nat.div_pos (Nat.gcd_le_left r has) hg
  have hd : 0 < d := Nat.div_pos (Nat.gcd_le_right (a * s) hr) hg
  have hcop : c.Coprime d := Nat.gcd_div_gcd_div_gcd_of_pos_left has
  have hgc : g * c = a * s := Nat.mul_div_cancel' (Nat.gcd_dvd_left (a * s) r)
  have hgd : g * d = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right (a * s) r)
  refine ⟨c, d, hc, hd, hcop, Nat.div_le_self _ _, ?_⟩
  have heq : (g : ℤ) * ((d : ℤ) * z - (c : ℤ) * t) =
      (r : ℤ) * z - (a * s : ℕ) * (t : ℤ) := by
    have hgcZ : (g : ℤ) * c = (a * s : ℕ) := by exact_mod_cast hgc
    have hgdZ : (g : ℤ) * d = r := by exact_mod_cast hgd
    nlinarith only [congrArg (fun w : ℤ ↦ w * t) hgcZ, congrArg (fun w : ℤ ↦ w * z) hgdZ]
  have hbound : (g : ℤ) * |(d : ℤ) * z - (c : ℤ) * t| ≤ ((r + 2 * s) * (L + 1) : ℕ) := by
    calc
      _ = |(g : ℤ) * ((d : ℤ) * z - (c : ℤ) * t)| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) g)]
      _ = _ := congrArg abs heq
      _ ≤ _ := scaled_offset_bound hx hgeom i hbase
  have hmono := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ g by exact_mod_cast hg)
    (abs_nonneg ((d : ℤ) * z - (c : ℤ) * t))
  simpa only [one_mul] using hmono.trans hbound

theorem bounded_height {a r s Q x z L t : ℕ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (hrQ : r ≤ Q) (hsQ : s ≤ Q) (hB : 3 * Q ≤ L + 1) (hx : 0 < x)
    (hgeom : EnlargedPairGeometry.Geometric r s x z L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    ∃ c d : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ (L + 1) ^ 2 ∧
      |h| ≤ ((L + 1) ^ 2 : ℕ) ∧ (d : ℤ) * z = (c : ℤ) * t + h := by
  obtain ⟨c, d, hc, hd, hcop, hdr, habs⟩ := reduced_affine_data ha hr hs hx hgeom i hbase
  have hscale : r + 2 * s ≤ L + 1 := by omega
  have hpow : L + 1 ≤ (L + 1) ^ 2 := le_self_pow (by omega) (by decide : 2 ≠ 0)
  have hheight : (r + 2 * s) * (L + 1) ≤ (L + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right (L + 1) hscale
  refine ⟨c, d, (d : ℤ) * z - (c : ℤ) * t, hc, hd, hcop, ?_, ?_, ?_⟩
  · exact hdr.trans ((show r ≤ L + 1 by omega).trans hpow)
  · exact habs.trans (by exact_mod_cast hheight)
  · ring

theorem bounded_polynomial_height {a r s K x z L t : ℕ} (ha : 0 < a) (hr : 0 < r) (hs : 0 < s)
    (hrB : r ≤ (L + 1) ^ K) (hsB : s ≤ (L + 1) ^ K) (hB : 3 ≤ L + 1) (hx : 0 < x)
    (hgeom : EnlargedPairGeometry.Geometric r s x z L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    ∃ c d : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ (L + 1) ^ (K + 2) ∧
      |h| ≤ ((L + 1) ^ (K + 2) : ℕ) ∧ (d : ℤ) * z = (c : ℤ) * t + h := by
  obtain ⟨c, d, hc, hd, hcop, hdr, habs⟩ := reduced_affine_data ha hr hs hx hgeom i hbase
  have hscale : r + 2 * s ≤ 3 * (L + 1) ^ K := by omega
  have hheight : (r + 2 * s) * (L + 1) ≤ (L + 1) ^ (K + 2) := by
    calc
      _ ≤ (3 * (L + 1) ^ K) * (L + 1) := Nat.mul_le_mul_right _ hscale
      _ = 3 * (L + 1) ^ (K + 1) := by rw [pow_succ]; ring
      _ ≤ (L + 1) * (L + 1) ^ (K + 1) := Nat.mul_le_mul_right _ hB
      _ = _ := by rw [pow_succ (L + 1) (K + 1)]; ring
  refine ⟨c, d, (d : ℤ) * z - (c : ℤ) * t, hc, hd, hcop, ?_, ?_, ?_⟩
  · exact hdr.trans (hrB.trans (Nat.pow_le_pow_right (by omega) (by omega : K ≤ K + 2)))
  · exact habs.trans (by exact_mod_cast hheight)
  · ring

end PaperP1.GeometricAlignedTargetData
