module

public import PaperP1.Asymptotics.OneTargetLogDenseCount
public import PaperP1.Model.OneTargetCrossing
public import PaperP1.Model.TwoTargetPrimitiveData

/-! # Unconditional subpower count of dense effective targets above an actual finite source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseEffectiveTargetCount

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.FiniteFamilyEnumeration

theorem uniform_count (s : ℕ) (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N →
      ∀ S : Finset ℕ, S ⊆ dyadicBlock N →
      (∀ z ∈ S, η * L ≤ (OneTargetCrossing.rank e L z : ℝ)) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨L₀, _hL₀, NC, _hNC, hc⟩ := OneTargetLogDenseCount.uniform_count s 1 2
    CriticalBandScale.upperScale η ε (by norm_num) CriticalBandScale.upperScale_pos.le hη hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (L₀ + 1)
  refine ⟨3 + NC + NG, by omega, ?_⟩
  intro N hN L hband e he heG S hSG hdense
  have hgeom := hg N (by omega) L hband
  have hL : L₀ ≤ L := by omega
  let x := centres e he
  have hx (i : Fin s) : x i ∈ dyadicBlock N := centres_mem (dyadicBlock N) e he heG i
  have hx2 (i : Fin s) : 2 ≤ x i := by have hh := (mem_Ico.mp (hx i)).1; omega
  have hheight (i : Fin s × Fin (L + 1)) : FixedSourceCertificate.sourceValues x (L + 1) i ≤ N ^ 2 := by
    have hh := (mem_Ico.mp (hx i.1)).2
    have hi := i.2.isLt
    have hwidth : L ≤ N := by omega
    have hcap : FixedSourceCertificate.sourceValues x (L + 1) i ≤ 3 * N := by
      unfold FixedSourceCertificate.sourceValues
      omega
    have hN3 : 3 ≤ N := by omega
    exact hcap.trans (by nlinarith only [Nat.mul_le_mul_left N hN3])
  have hspace : OneTargetCrossing.sourceSpace e L = ⨆ i, squareClassSpace (x i) L :=
    TwoTargetPrimitiveData.source_enumeration e L he
  apply hc N (by omega) L hL hgeom.2.2.2.2.2 x hx2 hheight
    (OneTargetCrossing.sourceSpace e L) hspace.le S
  intro z hz
  have hzlo := (mem_Ico.mp (hSG hz)).1
  have hzhi := (mem_Ico.mp (hSG hz)).2
  refine ⟨by omega, ?_, ?_, ?_⟩
  · simpa only [one_mul] using (show (N : ℝ) ≤ z by exact_mod_cast hzlo)
  · exact_mod_cast hzhi.le
  · rw [inf_comm]
    exact hdense z hz

end PaperP1.DenseEffectiveTargetCount
