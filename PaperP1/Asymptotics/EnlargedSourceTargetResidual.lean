module

public import PaperP1.Asymptotics.TwoProgressionSublinear
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Arithmetic.EnlargedSourceTargetGeometry

/-! # Uniform sublinear residual above enlarged sources with one actual source vertex -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedSourceTargetResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.ScaledTargetValues PaperP1.TargetUnionGeometry PaperP1.TwoProgressionPrimeRows
  PaperP1.CriticalBandScale

theorem row_rank_sublinear (C ε : ℝ) (hε : 0 < ε) {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (J : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L c d x y z t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < c → 0 < d → d ≤ (L + 1) ^ J →
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      EnlargedPairGeometry.Geometric a b x y L →
      ∀ i : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
        ∀ h : ℤ, |h| ≤ ((L + 1) ^ J : ℕ) → (d : ℤ) * z = (c : ℤ) * t + h →
        (Module.finrank F₂ (CoverGraphResolution.rowSolutions
          (PrimeRowComponents.rows (allValues a b c d x y z L)
            (exceptionalPrimes (6 * b * (L + 1)) c (a * b * d)))) : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  let c₀ : ℝ := 1 / (2 * upperScale)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; exact div_pos zero_lt_one (mul_pos (by norm_num) upperScale_pos)
  have hD : (0 : ℝ) < ((J + 2 : ℕ) : ℝ) := by positivity
  obtain ⟨Bcore, hcore⟩ := TwoProgressionSublinear.row_rank_sublinear c₀ ((J + 2 : ℕ) : ℝ)
    (6 * b) 3 ε (2 * J + 1) hc₀ hD hε
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C
    (max Bcore (1024 * a * b + 2 * a * a * b + 2))
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C
    ((64 * a * b + 8 : ℕ) : ℝ) (by positivity) (J + 1)
  obtain ⟨Nsource, hsource⟩ := CriticalPolynomialScale.source_size_eventually C
    (a * EnlargedSourceTargetGeometry.sourceScale a b) J
  refine ⟨max Ngeom (max Npoly Nsource), ?_⟩
  intro N hN L c d x y z t hcrit hc hd hdH hx hy hz hsourceGeom i hbaseX h hh htarget
  let B : ℕ := L + 1
  let H : ℕ := B ^ J
  obtain ⟨hNtwo, hBlarge, hBtwo, _hBN, _, hBhi⟩ := hgeom N ((le_max_left _ _).trans hN) L hcrit
  have hBcore : Bcore ≤ B := (le_max_left _ _).trans hBlarge
  have hBcoeff : 2 * a * a * b ≤ B := by have := (le_max_right _ _).trans hBlarge; omega
  have hBwidth : 512 * (2 * a) * b ≤ B := by
    have hbound : 1024 * a * b ≤ B := by have := (le_max_right _ _).trans hBlarge; omega
    nlinarith only [hbound]
  have hb : 0 < b := ha.trans_le hab
  have hxpos : 0 < x := by have := (mem_Ico.mp hx).1; omega
  have hypos : 0 < y := by have := (mem_Ico.mp hy).1; omega
  have hzpos : 0 < z := by have := (mem_Ico.mp hz).1; omega
  have hsize := hsource N ((le_max_right Npoly Nsource).trans ((le_max_right _ _).trans hN))
    L H hcrit le_rfl
  have hcH : c ≤ 2 * a * H := EnlargedSourceTargetGeometry.numerator_bound
    (by omega : 0 < N) ha hx hy hz hsourceGeom i hbaseX hdH hh htarget hsize
  have hpolyNat : (64 * a * b + 8) * B ^ (J + 1) < N := by
    exact_mod_cast hpoly N ((le_max_left Npoly Nsource).trans ((le_max_right _ _).trans hN)) L hcrit
  have hradius := radius_polynomial (a := 2 * a) (b := b) (H := H) (L := L) (J := J) le_rfl
  change radius (2 * a) b H L ≤ 4 * (2 * a) * b * B ^ (J + 1) at hradius
  have hBp : 1 ≤ B ^ (J + 1) := by have h := pow_pos (show 0 < B by omega) (J + 1); omega
  have hlarge : 8 * radius (2 * a) b H L + 8 ≤ N := by
    have hmul := Nat.mul_le_mul_left 8 hradius
    nlinarith only [hmul, hpolyNat, hBp]
  have hbase := base_geometry hb hc (mem_Ico.mp hx).1 hlarge i
  let U : ℕ := base (2 * a) b c H x L i
  let R : ℕ := 2 * radius (2 * a) b H L
  have hHpos : 0 < H := pow_pos (show 0 < B by omega) J
  have hRpos : 0 < radius (2 * a) b H L := by unfold radius; positivity
  have hR : 1 ≤ R := by dsimp [R]; omega
  have hU : 2 * R ≤ U := by dsimp [R, U]; nlinarith only [hbase.2.2]
  have hlogU : c₀ * B ≤ Real.log U :=
    CriticalWindowGeometry.log_base_lower (by omega : 4 ≤ N) hbase.2.1 hBhi
  have hlogR := logarithmic_width (by omega : 0 < 2 * a) hb hHpos
    (show H ≤ (L + 1) ^ J from le_rfl) hBwidth
  have hradOld : EnlargedPairGeometry.radius b L ≤ radius (2 * a) b H L := by
    have hmul := Nat.mul_le_mul_right (b * B) (show 1 ≤ a * H from Nat.mul_pos ha hHpos)
    unfold EnlargedPairGeometry.radius radius
    change 3 * (b * B) ≤ 4 * (2 * a * b * (H * B))
    nlinarith only [hmul]
  have hlargeOld : 8 * EnlargedPairGeometry.radius b L + 8 ≤ N := by omega
  have hbaseOld := EnlargedPairGeometry.base_geometry hb (mem_Ico.mp hx).1 hlargeOld
  apply hcore B hBcore (allValues a b c d x y z L) (6 * b * B) c (a * b * d)
    (EnlargedPairGeometry.base b x L) (z - 1) (2 * EnlargedPairGeometry.radius b L) L U R
  · have hmul := Nat.mul_le_mul_right B (show 1 ≤ 6 * b by omega)
    simpa only [one_mul] using hmul
  · push_cast
    rfl
  · exact hc
  · exact Nat.mul_pos (Nat.mul_pos ha hb) hd
  · exact coefficient_product hcH hdH le_rfl hBcoeff
  · unfold EnlargedPairGeometry.radius
    dsimp only [B]
    exact le_of_eq (by ring)
  · have hmul := Nat.mul_le_mul_right B (show 1 ≤ 6 * b by omega)
    exact (Nat.le_succ L).trans (by simpa only [one_mul] using hmul)
  · exact EnlargedSourceTargetGeometry.two_progressions hab hxpos hypos hzpos hsourceGeom hbaseOld.1
  · intro n hn
    exact (EnlargedSourceTargetGeometry.interval_bounds hab hxpos hypos hzpos hcH hdH
      hsourceGeom i h hh hbaseX htarget hbase.1 n hn).1
  · intro n hn
    exact (EnlargedSourceTargetGeometry.interval_bounds hab hxpos hypos hzpos hcH hdH
      hsourceGeom i h hh hbaseX htarget hbase.1 n hn).2
  · exact hR
  · exact hU
  · exact hlogU
  · exact hlogR
  · exact_mod_cast all_card_le (L := L) ha hb hd hxpos hypos hzpos

end PaperP1.EnlargedSourceTargetResidual
