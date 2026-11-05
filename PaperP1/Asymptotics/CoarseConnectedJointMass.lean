module

public import PaperP1.Asymptotics.ConnectedSeedCatalog
public import PaperP1.Asymptotics.VariableSeedMassPropagation

/-! # Every fixed bounded range of actual connected families of size at least three has joint mass N⁻¹ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedJointMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_catalog_extensions (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ G ∧ I.card = r ∧ ∃ D ∈ ConnectedSeedCatalog.families G L R, D ⊆ I) →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NS, _hNS, hs⟩ := ConnectedSeedCatalog.uniform_mass R C (ε / 4) (by positivity)
  have hprop (i : Fin (R + 1)) := VariableSeedMassPropagation.uniform_mass i.val C (ε / 4) (by positivity)
  choose NR hr using hprop
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (R.factorial : ℝ)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NS + NG + NF + univ.sup NR, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF
  let i : Fin (R + 1) := ⟨r, by omega⟩
  have hiN : NR i ≤ univ.sup NR := le_sup (f := NR) (mem_univ i)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let S := (ConnectedSeedCatalog.families G L R).filter fun D ↦ D.card ≤ r
  have hsource (D : Finset ℕ) (hD : D ∈ S) : D ⊆ dyadicBlock N ∧ 1 ≤ D.card ∧ D.card ≤ r := by
    obtain ⟨hDC, hcard⟩ := mem_filter.mp hD
    have hd := ConnectedSeedCatalog.family_data G L R D hDC
    exact ⟨hd.1.trans hG, by omega, hcard⟩
  have htarget (I : Finset ℕ) (hI : I ∈ F) :
      I ⊆ dyadicBlock N ∧ I.card = r ∧ ∃ D ∈ S, D ⊆ I := by
    obtain ⟨hsub, hcard, D, hD, hDI⟩ := hF I hI
    exact ⟨hsub.trans hG, hcard, D, mem_filter.mpr ⟨hD, by have h := card_le_card hDI; omega⟩, hDI⟩
  have hseed : (∑ D ∈ S, infiniteJointMoment L D) ≤ (N : ℝ) ^ (-1 + ε / 4) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun D _ _ ↦ infiniteJointMoment_nonneg L D)).trans
      (hs N (by omega) L hband G hG)
  have hraw := hr i N (by omega) L hL hband S hsource F htarget
  have hfact : (r.factorial : ℝ) ≤ R.factorial := by exact_mod_cast Nat.factorial_le hcap
  calc
    _ ≤ (r.factorial : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-1 + ε / 4) := hraw.trans
      (mul_le_mul_of_nonneg_left hseed (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)))
    _ ≤ (R.factorial : ℝ) * (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (-1 + ε / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfact (Real.rpow_nonneg hn.le _))
        (Real.rpow_nonneg hn.le _)
    _ = (R.factorial : ℝ) * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

theorem uniform_range (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      F ⊆ connectedFamilies G L r →
      (∑ I ∈ F, infiniteJointMoment L I) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨N₀, hN₀, h⟩ := uniform_catalog_extensions R C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF
  apply h N hN L hband r hthree hcap G hG F
  intro I hI
  obtain ⟨hIG, hconn⟩ := mem_filter.mp (hF hI)
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hIG
  obtain ⟨D, hD, hDI⟩ := ConnectedSeedCatalog.cover G L R I hsub (by omega) (by omega) hconn
  exact ⟨hsub, hcard, D, hD, hDI⟩

theorem uniform_compatible_activity (R : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ r : ℕ, 3 ≤ r → r ≤ R →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      F ⊆ connectedFamilies G L r → (∀ I ∈ F, 0 < infiniteJointMoment L I) →
      (∑ I ∈ F, |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨NJ, _hNJ, hj⟩ := uniform_range R C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 : ℝ) ^ R)
    (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NJ + NG + NF, by omega, ?_⟩
  intro N hN L hband r hthree hcap G hG F hF hq
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hmass := hj N (by omega) L hband r hthree hcap G hG F hF
  have hpoint (I : Finset ℕ) (hI : I ∈ F) :
      |infiniteCenteredCoefficient L I| ≤ (2 : ℝ) ^ R * infiniteJointMoment L I := by
    have hcard := (mem_powersetCard.mp (mem_filter.mp (hF hI)).1).2
    have hp : (2 : ℝ) ^ I.card ≤ (2 : ℝ) ^ R := pow_le_pow_right₀ (by norm_num) (by omega)
    exact (CompatibleTripleJointBound.centered_compatible_bound L I hL (hq I hI)).trans
      (mul_le_mul_of_nonneg_right hp (infiniteJointMoment_nonneg L I))
  calc
    _ ≤ ∑ I ∈ F, (2 : ℝ) ^ R * infiniteJointMoment L I := sum_le_sum hpoint
    _ = (2 : ℝ) ^ R * ∑ I ∈ F, infiniteJointMoment L I := by rw [mul_sum]
    _ ≤ (2 : ℝ) ^ R * (N : ℝ) ^ (-1 + ε / 2) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ ≤ _ := by
      convert hf N (by omega) using 1
      congr 1
      ring

end PaperP1.CoarseConnectedJointMass
