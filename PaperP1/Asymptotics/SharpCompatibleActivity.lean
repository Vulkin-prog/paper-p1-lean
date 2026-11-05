module

public import PaperP1.Asymptotics.SharpConnectedSeedCatalog
public import PaperP1.Asymptotics.VariableSeedMassPropagation

/-! # Every fixed compatible connected activity reduces to the actual third absolute activity -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharpCompatibleActivity

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      F ⊆ connectedFamilies G L r → (∀ I ∈ F, 0 < infiniteJointMoment L I) →
      (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤
        (N : ℝ) ^ ε * CompatibleActivitySplit.absolute L (connectedFamilies G L 3) +
        (N : ℝ) ^ (-4 / 3 + ε) := by
  classical
  obtain ⟨NS, _hNS, hs⟩ := SharpConnectedSeedCatalog.uniform_mass R C (ε / 4) (by positivity)
  have hprop (i : Fin (R + 1)) := VariableSeedMassPropagation.uniform_mass i.val C (ε / 4) (by positivity)
  choose NR hr using hprop
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  let K : ℝ := (2 : ℝ) ^ R * R.factorial
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption K 0 (ε / 2) (by positivity)
  refine ⟨10 + NS + NG + NF + univ.sup NR, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF hq
  let i : Fin (R + 1) := ⟨r, by omega⟩
  have hiN : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let A3 := CompatibleActivitySplit.absolute L (connectedFamilies G L 3)
  let S := (VariableConnectedSeedCatalog.families G L R ((ε / 4) / 8)).filter fun D ↦ D.card ≤ r
  have hsource (D : Finset ℕ) (hD : D ∈ S) : D ⊆ dyadicBlock N ∧ 1 ≤ D.card ∧ D.card ≤ r := by
    obtain ⟨hDC, hcard⟩ := mem_filter.mp hD
    have hd := VariableConnectedSeedCatalog.family_data G L R ((ε / 4) / 8) D hDC
    exact ⟨hd.1.trans hG, by omega, hcard⟩
  have htarget (I : Finset ℕ) (hI : I ∈ F) :
      I ⊆ dyadicBlock N ∧ I.card = r ∧ ∃ D ∈ S, D ⊆ I := by
    obtain ⟨hIG, hconn⟩ := mem_filter.mp (hF hI)
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
    obtain ⟨D, hD, hDI⟩ := VariableConnectedSeedCatalog.cover G L R ((ε / 4) / 8)
      (by positivity) I hsub (by omega) (by omega) hconn
    exact ⟨hsub.trans hG, hcard, D, mem_filter.mpr ⟨hD, by have h := card_le_card hDI; omega⟩, hDI⟩
  have hseed : (∑ D ∈ S, infiniteJointMoment L D) ≤
      (N : ℝ) ^ (ε / 4) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 4) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun D _ _ ↦ infiniteJointMoment_nonneg L D)).trans
      (hs N (by omega) L hband G hG)
  have hraw := hr i N (by omega) L hL hband S hsource F htarget
  have hfact : (r.factorial : ℝ) ≤ R.factorial := by exact_mod_cast Nat.factorial_le hcap
  have hA3 : 0 ≤ A3 := sum_nonneg fun D _ ↦ abs_nonneg _
  have hmass : (∑ I ∈ F, infiniteJointMoment L I) ≤ (R.factorial : ℝ) *
      ((N : ℝ) ^ (ε / 2) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 2)) := by
    calc
      _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 4) *
          ((N : ℝ) ^ (ε / 4) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 4)) :=
        hraw.trans (mul_le_mul_of_nonneg_left hseed (by positivity))
      _ ≤ (R.factorial : ℝ) * (N : ℝ) ^ (ε / 4) *
          ((N : ℝ) ^ (ε / 4) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 4)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfact (by positivity)) (by positivity)
      _ = _ := by
        have hpow1 : (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) = (N : ℝ) ^ (ε / 2) := by
          rw [← Real.rpow_add hn]
          congr 1
          ring
        have hpow2 : (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-4 / 3 + ε / 4) =
            (N : ℝ) ^ (-4 / 3 + ε / 2) := by
          rw [← Real.rpow_add hn]
          congr 1
          ring
        rw [mul_assoc, mul_add, ← mul_assoc, hpow1, hpow2]
  have hpoint (I : Finset ℕ) (hI : I ∈ F) :
      |infiniteCenteredCoefficient L I| ≤ (2 : ℝ) ^ R * infiniteJointMoment L I := by
    have hcard := (mem_powersetCard.mp (mem_filter.mp (hF hI)).1).2
    exact (CompatibleTripleJointBound.centered_compatible_bound L I hL (hq I hI)).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega)) (infiniteJointMoment_nonneg L I))
  have hconstant : K ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  calc
    _ ≤ ∑ I ∈ F, (2 : ℝ) ^ R * infiniteJointMoment L I := sum_le_sum hpoint
    _ = (2 : ℝ) ^ R * ∑ I ∈ F, infiniteJointMoment L I := by rw [mul_sum]
    _ ≤ K * ((N : ℝ) ^ (ε / 2) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 2)) := by
      have h := mul_le_mul_of_nonneg_left hmass (by positivity : (0 : ℝ) ≤ 2 ^ R)
      exact h.trans_eq (by dsimp [K]; ring)
    _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (ε / 2) * A3 + (N : ℝ) ^ (-4 / 3 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ = _ := by
      rw [mul_add, ← mul_assoc, ← Real.rpow_add hn, add_halves, ← Real.rpow_add hn]
      congr 1
      congr 1
      ring

end PaperP1.SharpCompatibleActivity
