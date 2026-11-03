module

public import PaperP1.Asymptotics.EnlargedAlignedPairTheorem
public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # Every strongly aligned effective pair has an exact unit in one fixed finite channel set -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongAlignedUnitChannels

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model

theorem bounded_channels (θ : ℝ) (hθ : 0 < θ) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ y z : ℕ,
      y ∈ dyadicBlock N → z ∈ dyadicBlock N →
      θ * L < (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) →
      CompressedTargetAlignment.Aligned 1 y z L →
      ∃ a b : ℕ, 0 < a ∧ a ≤ b ∧ b ≤ Q ∧
        ((NormalizedUnitCount.units a b y z L).Nonempty ∨
          (NormalizedUnitCount.units a b z y L).Nonempty) := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < θ / 4 by positivity)
  let Q := max 1 n
  have hQdiv : 1 / ((Q + 1 : ℕ) : ℝ) ≤ θ / 4 := by
    have hmono : (n : ℝ) + 1 ≤ ((Q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show n + 1 ≤ Q + 1 by dsimp [Q]; omega)
    exact (one_div_le_one_div_of_le (by positivity) hmono).trans hn.le
  refine ⟨Q, le_max_left _ _, fun C ↦ ?_⟩
  obtain ⟨NR, hr⟩ := EnlargedAlignedPairTheorem.uniform_bounds C (θ / 4) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NR + NG, by omega, ?_⟩
  intro N hN L hband y z hy hz hstrong halign
  obtain ⟨a, b, ha, hb, hcop, haH, hbH, hgeom⟩ := halign
  have hGeom : EnlargedPairGeometry.Geometric a b y z L := by
    simpa only [EnlargedPairGeometry.Geometric, one_mul, abs_sub_comm] using hgeom
  have hrank := hr N (by omega) L a b y z hband ha hb hcop (max_le haH hbH) hy hz hGeom
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hB : ((L + 1 : ℕ) : ℝ) ≤ 2 * (L : ℝ) := by exact_mod_cast (show L + 1 ≤ 2 * L by omega)
  have herror := mul_le_mul_of_nonneg_left hB (show 0 ≤ θ / 4 by positivity)
  have hmax : max a b ≤ Q := by
    by_contra hnQ
    have hmNat : Q + 1 ≤ max a b := by omega
    have hmR : ((Q + 1 : ℕ) : ℝ) ≤ (max a b : ℝ) := by exact_mod_cast hmNat
    have hcoef : 1 / (max a b : ℝ) ≤ θ / 4 :=
      (one_div_le_one_div_of_le (by positivity) hmR).trans hQdiv
    have hdiv : (L : ℝ) / max a b ≤ (θ / 4) * L := by
      have h := mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg L)
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, Nat.cast_max] using h
    have hpair := hrank.2.2
    change (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤
      (L : ℝ) / max a b + (θ / 4) * ((L + 1 : ℕ) : ℝ) at hpair
    have hpositive := mul_pos hθ hLpos
    nlinarith only [hstrong, hpair, hdiv, herror, hpositive]
  have hu : (NormalizedUnitCount.units a b y z L).Nonempty := by
    by_contra hnone
    have hzero : (NormalizedUnitCount.units a b y z L).card = 0 :=
      Nat.eq_zero_of_not_pos (fun h ↦ hnone (card_pos.mp h))
    have hloss := hrank.1
    rw [hzero] at hloss
    norm_num only [Nat.zero_sub, Nat.cast_zero, zero_add] at hloss
    have hypos : 0 < y := by have h := (mem_Ico.mp hy).1; omega
    have hzpos : 0 < z := by have h := (mem_Ico.mp hz).1; omega
    have hinter : (Module.finrank F₂ ↥(squareClassSpace y L ⊓ squareClassSpace z L) : ℝ) ≤
        NormalizedPairRankLoss.pairLoss y z L := by
      exact_mod_cast NormalizedPairRankLoss.intersection_rank_le_loss hypos hzpos
    have hpositive := mul_pos hθ hLpos
    nlinarith only [hstrong, hinter, hloss, herror, hpositive]
  by_cases hab : a ≤ b
  · exact ⟨a, b, ha, hab, (le_max_right _ _).trans hmax, Or.inl hu⟩
  · obtain ⟨ij, hij⟩ := hu
    have hswap : (NormalizedUnitCount.units b a z y L).Nonempty :=
      ⟨(ij.2, ij.1), NormalizedUnitCount.mem_units.mpr (NormalizedUnitCount.mem_units.mp hij).symm⟩
    exact ⟨b, a, hb, le_of_not_ge hab, (le_max_left _ _).trans hmax, Or.inr hswap⟩

end PaperP1.StrongAlignedUnitChannels
