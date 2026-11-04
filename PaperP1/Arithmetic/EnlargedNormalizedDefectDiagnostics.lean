module

public import PaperP1.Arithmetic.EnlargedPairGeometry
public import PaperP1.Arithmetic.NormalizedPrivateDefects
public import PaperP1.Arithmetic.NormalizedPairRankLoss
public import PaperP1.Arithmetic.IntervalResidualKernel

/-! # Literal defect witnesses for every enlarged normalized pair

The arithmetic interval uses its saturated natural base. No lower source-size
or exact-unit premise is needed for these finite kernel and privacy criteria.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedNormalizedDefectDiagnostics

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.NormalizedWindowSets
  PaperP1.EnlargedPairGeometry PaperP1.DefectivePredicate PaperP1.GoodEdgeCompression
  PaperP1.IntervalResidualKernel PaperP1.NormalizedPairRankLoss PaperP1.NormalizedUnitCount

theorem interval_bounds_all {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hg : Geometric a b x y L) {n : ℕ} (hn : n ∈ NormalizedWindowSets.union a b x y L) :
    base b x L ≤ n ∧ n ≤ base b x L + 2 * radius b L := by
  by_cases hbase : radius b L ≤ b * x
  · exact interval_bounds hab hx hy hg hbase n hn
  · have hnBounds := abs_le.mp (union_abs_bound hab hx hy hg n hn)
    have hhi : n ≤ b * x + radius b L := by
      have hi : (n : ℤ) ≤ ((b * x : ℕ) : ℤ) + (radius b L : ℤ) := by linarith only [hnBounds.2]
      exact_mod_cast hi
    have hz : base b x L = 0 := by unfold base; omega
    simp only [hz, Nat.zero_add]
    omega

theorem normalized_dist_bound {a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hg : Geometric a b x y L) {n m : ℕ}
    (hn : n ∈ NormalizedWindowSets.union a b x y L) (hm : m ∈ NormalizedWindowSets.union a b x y L) :
    Nat.dist n m ≤ 2 * radius b L := by
  have hnBounds := abs_le.mp (union_abs_bound hab hx hy hg n hn)
  have hmBounds := abs_le.mp (union_abs_bound hab hx hy hg m hm)
  have hnm : n ≤ m + 2 * radius b L := by
    have hi : (n : ℤ) ≤ (m : ℤ) + 2 * (radius b L : ℤ) := by linarith only [hnBounds.2, hmBounds.1]
    exact_mod_cast hi
  have hmn : m ≤ n + 2 * radius b L := by
    have hi : (m : ℤ) ≤ (n : ℤ) + 2 * (radius b L : ℤ) := by linarith only [hmBounds.2, hnBounds.1]
    exact_mod_cast hi
  rw [Nat.dist]
  omega

theorem normalized_private_iff {H a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hg : Geometric a b x y L) (hcut : 2 * radius b L < H) :
    PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L) ↔
      ∀ n ∈ NormalizedWindowSets.union a b x y L, ¬HDefective H n := by
  apply PaperP1.NormalizedPrivateDefects.privateAbove_iff_nondefective
  intro n hn m hm _hne
  exact (normalized_dist_bound hab hx hy hg hn hm).trans_lt hcut

theorem normalized_bad_witness {H a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hg : Geometric a b x y L) (hcut : 2 * radius b L < H)
    (hbad : ¬PrivateAbove (H : ℝ) (NormalizedWindowSets.union a b x y L)) :
    ∃ n ∈ NormalizedWindowSets.union a b x y L, HDefective H n := by
  classical
  rw [normalized_private_iff hab hx hy hg hcut] at hbad
  push Not at hbad
  exact hbad

theorem kernel_defect_witness {H a b x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hg : Geometric a b x y L) (hcut : 2 * radius b L ≤ H)
    (hpos : 0 < Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L))) :
    ∃ n ∈ NormalizedWindowSets.union a b x y L, HDefective H n := by
  classical
  have hS : NormalizedWindowSets.union a b x y L ⊆ Icc (base b x L) (base b x L + 2 * radius b L) := by
    intro n hn
    exact mem_Icc.mpr (interval_bounds_all hab hx hy hg hn)
  have hle : Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) ≤
      (selectedDefects (NormalizedWindowSets.union a b x y L) H).card :=
    (Submodule.finrank_mono (fullKernel_le_large (NormalizedWindowSets.union a b x y L) H)).trans
      (rank_le_selected_defects hcut hS)
  obtain ⟨n, hn⟩ := card_pos.mp (hpos.trans_le hle)
  exact ⟨n, (mem_filter.mp hn).1, (mem_filter.mp hn).2⟩

theorem extra_loss_witness {H a b x y L : ℕ} (ha : 0 < a) (hab : a ≤ b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hg : Geometric a b x y L) (hcut : 2 * radius b L ≤ H)
    (hextra : (units a b x y L).card - 1 < pairLoss x y L) :
    ∃ n ∈ NormalizedWindowSets.union a b x y L, HDefective H n := by
  have hupper := loss_le_units_add_residual_all (L := L) ha (ha.trans_le hab) hx hy
  have hpos : 0 < Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by omega
  exact kernel_defect_witness hab (by omega) (by omega) hg hcut hpos

theorem loss_le_of_no_defects {H a b x y L : ℕ} (ha : 0 < a) (hab : a ≤ b) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hg : Geometric a b x y L) (hcut : 2 * radius b L ≤ H)
    (hgood : ∀ n ∈ NormalizedWindowSets.union a b x y L, ¬HDefective H n) :
    pairLoss x y L ≤ (units a b x y L).card - 1 := by
  by_contra h
  obtain ⟨n, hn, hd⟩ := extra_loss_witness ha hab hx hy hg hcut (by omega)
  exact hgood n hn hd

end PaperP1.EnlargedNormalizedDefectDiagnostics
