module

public import PaperP1.Arithmetic.AnchorKernelProduct
public import PaperP1.Asymptotics.AnchorThresholdBudget
public import PaperP1.Asymptotics.AnchorCertificateDegrees
public import PaperP1.Algebra.OldBlockSelections
public import PaperP1.Asymptotics.ComparableSplitProductCount

/-! # Actual projected relations force one of the counted certificate edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchorRelationCertificates

open Finset Filter PaperP1.Arithmetic PaperP1.LinearKernelFibres
  PaperP1.RankinSmallKernel PaperP1.AnchorCertificateGraph

theorem selected_relation {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (C t : ℕ) (hC : 1 ≤ C) (A E : ℝ) (hA : 1 < A)
    (hgap : (Fintype.card ρ : ℝ) < (t : ℝ) / 5) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      ∀ G : Finset ℕ, (∀ n ∈ G, W < n ∧ n ≤ C * N) → ∀ x ∈ G,
      ∀ z : ρ → ℕ, (∀ j, z j ∈ G) → ∀ S : Finset ℤ, ∀ T : ρ → Finset ℤ,
      (∀ u ∈ S, u.natAbs ≤ W) → (∀ j, ∀ v ∈ T j, v.natAbs ≤ W) →
      t ≤ (S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) <
        (truncatedKernel ((Real.log N) ^ A) (value x u) : ℝ)).card →
      (∑ u ∈ S, parityVec (value x u)) + (∑ j, ∑ v ∈ T j, parityVec (value (z j) v)) = 0 →
      ∃ j : ρ, z j ∈ outgoing G (C * N) W t ((Real.log N) ^ A) x := by
  classical
  have ht : 1 ≤ t := by
    have htR : (0 : ℝ) < t := by nlinarith only [hgap, (show (0 : ℝ) ≤ Fintype.card ρ from Nat.cast_nonneg _)]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast htR.ne')
  obtain ⟨Np, hNp⟩ := PaperP1.AnchorThresholdBudget.threshold_power C (Fintype.card ρ) t E hgap
  obtain ⟨Ny, hNy⟩ := eventually_atTop.mp
    (PaperP1.ModerateCertificateAsymptotic.cutoff_ge_log_eventually A (2 * E) hA)
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.PrimeLogBudget.log_nat_tendsto_atTop.eventually (eventually_ge_atTop 2))
  refine ⟨max 2 (max Np (max Ny Nl)), ?_⟩
  intro N hN W hwidth G hG x hx z hz S T hS hT hlarge hrelation
  let Y := (Real.log N) ^ A
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 2 ≤ Real.log N := hNl N (by omega)
  have hYone : 1 < Y := Real.one_lt_rpow (by linarith) (by linarith)
  have hY : (2 * W : ℝ) ≤ Y := by
    have hcut := hNy N (by omega)
    change 2 * E * Real.log N ≤ Y at hcut
    nlinarith only [hwidth, hcut]
  let L := S.filter fun u ↦ (N : ℝ) ^ (1 / 5 : ℝ) < (truncatedKernel Y (value x u) : ℝ)
  obtain ⟨T₀, hT₀L, hT₀card⟩ := exists_subset_card_eq hlarge
  let e : Fin t ≃ T₀ := (Finset.equivFinOfCardEq hT₀card).symm
  have heS : ∀ i, (e i).val ∈ S := fun i ↦ (mem_filter.mp (hT₀L (e i).property)).1
  have hepool : ∀ i, (e i).val ∈ PaperP1.BoundedIntegerMotifs.offsets W := by
    intro i
    exact (PaperP1.BoundedIntegerMotifs.subset_offsets W {(e i).val}).mpr (by
      intro u hu; rw [mem_singleton.mp hu]; exact hS (e i).val (heS i)) (mem_singleton_self _)
  let c : Code W t := fun i ↦ ⟨(e i).val, hepool i⟩
  have hinj : Function.Injective c := by
    intro i j hij
    have hvals : (e i).val = (e j).val :=
      congrArg (fun u : PaperP1.BoundedIntegerMotifs.offsets W ↦ u.val) hij
    exact e.injective (Subtype.ext hvals)
  have hsource : ∀ i, (c i).val ∈ S := heS
  have hlarge' : ∀ i, (N : ℝ) ^ (1 / 5 : ℝ) < (truncatedKernel Y (anchorValue x c i) : ℝ) :=
    fun i ↦ (mem_filter.mp (hT₀L (e i).property)).2
  have hX : 1 ≤ C * N := Nat.mul_pos (by omega : 0 < C) (by omega : 0 < N)
  have hthreshold : (threshold (C * N) W : ℝ) ^ Fintype.card ρ ≤ (N : ℝ) ^ ((1 / 5 : ℝ) * t) := by
    convert hNp N (by omega) W hwidth using 1
    congr 1
    ring
  obtain ⟨j, hj⟩ := PaperP1.AnchorKernelProduct.edge_of_selected_anchors (C * N) W t x Y N (1 / 5)
    c z S T hX ht (hG x hx).1 hn hYone hY hinj hsource hS hT hlarge' hthreshold hrelation
  exact ⟨j, mem_filter.mpr ⟨hz j, hj⟩⟩

variable {ν κ : Type*} [Fintype ν] [Fintype κ]

def ProjectedControl (G : Finset ℕ) (X W t : ℕ) (Y N : ℝ) : Prop :=
  ∀ x ∈ G, ∀ z : ν → ℕ, ∀ old : κ → ℕ,
    (∀ i, z i ∈ G) → (∀ j, old j ∈ G) →
    ∀ S : Finset ℤ, ∀ T : ν → Finset ℤ, ∀ O : κ → Finset ℤ,
    (∀ u ∈ S, u.natAbs ≤ W) → (∀ i, ∀ v ∈ T i, v.natAbs ≤ W) →
    (∀ j, ∀ v ∈ O j, v.natAbs ≤ W) →
    t ≤ (S.filter fun u ↦ N ^ (1 / 5 : ℝ) < (truncatedKernel Y (value x u) : ℝ)).card →
    (∑ u ∈ S, parityVec (value x u)) + (∑ i, ∑ v ∈ T i, parityVec (value (z i) v)) ∈
      PaperP1.OldSpaceProjection.oldSpace (PaperP1.OldBlockSelections.values old O) →
    ∃ j : ν ⊕ κ, Sum.elim z old j ∈ outgoing G X W t Y x

theorem projected_relations (C t : ℕ) (hC : 1 ≤ C) (A E : ℝ) (hA : 1 < A)
    (hgap : ((Fintype.card ν + Fintype.card κ : ℕ) : ℝ) < (t : ℝ) / 5) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      ∀ G : Finset ℕ, (∀ n ∈ G, W < n ∧ n ≤ C * N) →
      ProjectedControl (ν := ν) (κ := κ) G (C * N) W t ((Real.log N) ^ A) N := by
  classical
  obtain ⟨N₀, hN₀⟩ := selected_relation (ρ := ν ⊕ κ) C t hC A E hA (by
    simpa only [Fintype.card_sum] using hgap)
  refine ⟨N₀, ?_⟩
  intro N hN W hwidth G hG x hx z old hz hold S T O hS hT hO hlarge hprojected
  let u := (∑ a ∈ S, parityVec (value x a)) + (∑ i, ∑ a ∈ T i, parityVec (value (z i) a))
  obtain ⟨U, hU, hUeq⟩ := PaperP1.OldBlockSelections.exists_selections old O (-u)
    (PaperP1.OldSpaceProjection.oldSpace _ |>.neg_mem hprojected)
  have hrel : (∑ a ∈ S, parityVec (value x a)) +
      (∑ j : ν ⊕ κ, ∑ a ∈ Sum.elim T U j, parityVec (value (Sum.elim z old j) a)) = 0 := by
    rw [Fintype.sum_sum_type]
    change (∑ a ∈ S, parityVec (value x a)) +
      ((∑ i, ∑ a ∈ T i, parityVec (value (z i) a)) + (∑ j, ∑ a ∈ U j, parityVec (value (old j) a))) = 0
    rw [← add_assoc, hUeq]
    exact add_neg_cancel u
  have hzsum : ∀ j : ν ⊕ κ, Sum.elim z old j ∈ G := by
    intro j
    cases j with
    | inl i => exact hz i
    | inr j => exact hold j
  have hTsum : ∀ j : ν ⊕ κ, ∀ a ∈ Sum.elim T U j, a.natAbs ≤ W := by
    intro j a ha
    cases j with
    | inl i => exact hT i a ha
    | inr j => exact hO j a (hU j ha)
  exact hN₀ N hN W hwidth G hG x hx (Sum.elim z old) hzsum S (Sum.elim T U) hS hTsum hlarge hrel

theorem uniform_certificates (C t : ℕ) (hC : 1 ≤ C) (A E ε : ℝ)
    (hA : 1 < A) (hE : 0 ≤ E) (hε : 0 < ε)
    (hgap : ((Fintype.card ν + Fintype.card κ : ℕ) : ℝ) < (t : ℝ) / 5) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, (W : ℝ) ≤ E * Real.log N →
      ∀ G : Finset ℕ, (∀ n ∈ G, W < n ∧ n ≤ C * N) →
      (∀ x ∈ G,
        ((outgoing G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε) ∧
        ((incoming G (C * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε)) ∧
      ProjectedControl (ν := ν) (κ := κ) G (C * N) W t ((Real.log N) ^ A) N := by
  have ht : 1 ≤ t := by
    have htR : (0 : ℝ) < t := by nlinarith only [hgap, (show (0 : ℝ) ≤ (Fintype.card ν + Fintype.card κ : ℕ) from Nat.cast_nonneg _)]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast htR.ne')
  obtain ⟨Nd, hNd⟩ := PaperP1.AnchorCertificateDegrees.uniform_degrees C t hC ht A E ε (by linarith) hE hε
  obtain ⟨Nr, hNr⟩ := projected_relations (ν := ν) (κ := κ) C t hC A E hA hgap
  refine ⟨max Nd Nr, ?_⟩
  intro N hN W hwidth G hG
  exact ⟨hNd N (by omega) W hwidth G hG, hNr N (by omega) W hwidth G hG⟩

theorem critical_radius_control (a b A D Cband ε : ℝ) (t : ℕ)
    (ha : 0 < a) (hA : 1 < A) (hD : 0 ≤ D) (hε : 0 < ε)
    (hgap : ((Fintype.card ν + Fintype.card κ : ℕ) : ℝ) < (t : ℝ) / 5) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (W : ℝ) ≤ D * (L + 1 : ℕ) → (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      (∀ n ∈ G, ∀ u : ℤ, u.natAbs ≤ W →
        0 < (n : ℤ) + u ∧ (value n u : ℤ) = (n : ℤ) + u) ∧
      (∀ x ∈ G,
        ((outgoing G (K * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε) ∧
        ((incoming G (K * N) W t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε)) ∧
      ProjectedControl (ν := ν) (κ := κ) G (K * N) W t ((Real.log N) ^ A) N := by
  obtain ⟨K, hK, hcompare⟩ := PaperP1.ComparableLogBounds.exists_nat_comparison a b ha
  let E := D * PaperP1.CriticalBandScale.upperScale
  have hE : 0 ≤ E := mul_nonneg hD PaperP1.CriticalBandScale.upperScale_pos.le
  obtain ⟨Nc, hNc⟩ := uniform_certificates (ν := ν) (κ := κ) K t hK A E ε hA hE hε hgap
  obtain ⟨Nb, hNb⟩ := PaperP1.CriticalBandScale.critical_band_scale Cband
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre K E 1
  refine ⟨K, hK, max Nc (max Nb Nv), ?_⟩
  intro N hN L W G hband hwidth hG
  have hB := (hNb N (by omega) L hband).2
  have hwidthlog : (W : ℝ) ≤ E * Real.log N :=
    hwidth.trans (by simpa only [E, mul_assoc] using mul_le_mul_of_nonneg_left hB hD)
  have hWn : ∀ n ∈ G, W < n := by
    intro n hn
    exact hNv N (by omega) n W (hcompare N n (hG n hn).1 (hG n hn).2).1
      (by simpa only [Real.rpow_one] using hwidthlog)
  have hbox : ∀ n ∈ G, W < n ∧ n ≤ K * N := fun n hn ↦
    ⟨hWn n hn, (hcompare N n (hG n hn).1 (hG n hn).2).2⟩
  have hcontrols := hNc N (by omega) W hwidthlog G hbox
  refine ⟨?_, hcontrols⟩
  intro n hn u hu
  have habs : |u| ≤ (W : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast hu
  have hlo := (abs_le.mp habs).1
  have hnW : (W : ℤ) < n := by exact_mod_cast hWn n hn
  exact ⟨by omega, PaperP1.SmoothModulusHosts.value_cast n W u (hWn n hn) hu⟩

theorem companion_T6_3 (a b A D Cband ε : ℝ) (t : ℕ)
    (ha : 0 < a) (hA : 1 < A) (hD : 0 ≤ D) (hε : 0 < ε)
    (hgap : ((Fintype.card ν + Fintype.card κ : ℕ) : ℝ) < (t : ℝ) / 5) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ, ∀ G : Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (W : ℝ) ≤ D * (L + 1 : ℕ) → (∀ n ∈ G, a * N ≤ n ∧ (n : ℝ) ≤ b * N) →
      let R := W + (L + 1)
      (∀ n ∈ G, ∀ u : ℤ, u.natAbs ≤ R →
        0 < (n : ℤ) + u ∧ (value n u : ℤ) = (n : ℤ) + u) ∧
      (∀ x ∈ G,
        ((outgoing G (K * N) R t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε) ∧
        ((incoming G (K * N) R t ((Real.log N) ^ A) x).card : ℝ) ≤ (N : ℝ) ^ (1 / A + ε)) ∧
      ProjectedControl (ν := ν) (κ := κ) G (K * N) R t ((Real.log N) ^ A) N ∧
      2 * K * N * (L + 1) ≤ threshold (K * N) R := by
  obtain ⟨K, hK, N₀, hN₀⟩ := critical_radius_control (ν := ν) (κ := κ) a b A (D + 1) Cband ε t
    ha hA (by linarith) hε hgap
  refine ⟨K, hK, N₀, ?_⟩
  intro N hN L W G hband hwidth hG
  let R := W + (L + 1)
  have hRwidth : (R : ℝ) ≤ (D + 1) * (L + 1 : ℕ) := by
    dsimp [R]
    push_cast
    have hb := hwidth
    push_cast at hb
    nlinarith only [hb]
  have hcontrols := hN₀ N hN L R G hband hRwidth hG
  refine ⟨hcontrols.1, hcontrols.2.1, hcontrols.2.2, ?_⟩
  have hpool : L + 1 ≤ (PaperP1.BoundedIntegerMotifs.offsets R).card := by
    rw [PaperP1.BoundedIntegerMotifs.offsets_card]
    dsimp [R]
    omega
  simpa only [threshold, mul_assoc] using Nat.mul_le_mul_left (2 * K * N) hpool

end PaperP1.AnchorRelationCertificates
