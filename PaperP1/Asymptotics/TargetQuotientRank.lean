module

public import PaperP1.Asymptotics.TargetUnionResidual
public import PaperP1.Arithmetic.TargetWindowRank
public import PaperP1.Arithmetic.DyadicMatchBound

/-! # Actual asymptotic target quotient rank for polynomially bounded affine data -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TargetQuotientRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ScaledTargetValues
  PaperP1.NormalizedUnitCount PaperP1.FixedChannelGamma PaperP1.DyadicEndpointPairs
  PaperP1.TwoProgressionPrimeRows PaperP1.TargetWindowRank

theorem bounded_affine_rank (C ε : ℝ) (hε : 0 < ε) {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L c d x y z t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < c → 0 < d → c.Coprime d → d ≤ (L + 1) ^ J →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      (x + L ≤ z ∨ z + L ≤ x) → (y + L ≤ z ∨ z + L ≤ y) →
      (x, y) ∉ exceptional N a b L ((L + 1) + 2 * (L + 1) ^ J) →
      ∀ i j : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
        startCompleteVertexLabel y L j = b * t →
        ∀ h : ℤ, |h| ≤ ((L + 1) ^ J : ℕ) → (d : ℤ) * z = (c : ℤ) * t + h →
        ∀ Q : Finset ℕ, Q ⊆ (a * b).primeFactors →
        (deficiency Q x y z L : ℝ) ≤ (gammaReal a b + ε) * L := by
  obtain ⟨Nres, hres⟩ := TargetUnionResidual.row_rank_sublinear C (ε / 4) (by positivity) ha horder.le J
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (Nat.ceil (8 / ε) + 2)
  obtain ⟨Nsource, hsource⟩ := CriticalPolynomialScale.source_size_eventually C a J
  refine ⟨max Nres (max Ngeom Nsource), ?_⟩
  intro N hN L c d x y z t hcrit hc hd hcop hdH hx hy hz hsepX hsepY haway i j hbaseX hbaseY h hh htarget Q hQ
  obtain ⟨hNtwo, hBlarge, _, _, _, _⟩ :=
    hgeom N ((le_max_left Ngeom Nsource).trans ((le_max_right _ _).trans hN)) L hcrit
  have hNpos : 0 < N := by omega
  have hx2 : 2 ≤ x := hNtwo.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hNtwo.trans (mem_Ico.mp hy).1
  have hz2 : 2 ≤ z := hNtwo.trans (mem_Ico.mp hz).1
  have hbpos : 0 < b := by omega
  have hsize := hsource N ((le_max_right Ngeom Nsource).trans ((le_max_right _ _).trans hN))
    L ((L + 1) ^ J) hcrit le_rfl
  obtain ⟨hlo, hhi⟩ := DyadicMatchBound.ratio_outside_exceptional hNpos hx hy hz hd hdH hh
    i j hbaseX hbaseY htarget hsize haway
  have hQP : Q ⊆ exceptionalPrimes (2 * b * (L + 1)) c (a * b * d) :=
    hQ.trans (TargetUnionGeometry.source_primes_subset ha hbpos hc hd)
  have hfinite := TargetWindowRank.interior_bound hQP ha hb hab horder hc hd hcop hx2 hy2 hz2
    hsepX hsepY i j h hbaseX hbaseY htarget hlo hhi
  have hrow := hres N ((le_max_left _ _).trans hN) L c d x y z t hcrit hc hd hdH hx hy hz
    i j hbaseX hbaseY h hh htarget
  have hγ := gammaReal_le_two_thirds hab hb
  have hLlarge : Nat.ceil (8 / ε) ≤ L := by omega
  have hLreal : 8 / ε ≤ (L : ℝ) := (Nat.le_ceil (8 / ε)).trans (by exact_mod_cast hLlarge)
  have hεL : 8 ≤ ε * L := by
    have hmul := (div_le_iff₀ hε).mp hLreal
    nlinarith only [hmul]
  have hLpos : 1 ≤ L := by omega
  have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have hsmall := mul_le_mul_of_nonneg_left hB (show 0 ≤ ε / 4 by positivity)
  norm_num only [Nat.cast_add, Nat.cast_one] at hfinite hrow hsmall
  nlinarith only [hfinite, hrow, hγ, hεL, hsmall]

end PaperP1.TargetQuotientRank
