module

public import PaperP1.Arithmetic.MultiAnchorSaturation

/-! # Actual incoming and outgoing t-anchor saturation counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorSaturationCounts

open Finset PaperP1.MultiAnchorSaturation PaperP1.MultiAnchorPrimeBudget
open PaperP1.SaturationPrimes (value receiverPrimes mem_receiverPrimes mem_largePrimes
  receiverPrimes_prime value_bounds)

def anchorOffsets (t B : ℕ) : Finset (Fin t → Fin B) :=
  univ.filter Function.Injective

def outgoingCover (t B N : ℕ) (Y : ℝ) (x : ℕ) : Finset ℕ :=
  (anchorOffsets t B).biUnion fun u ↦ PaperP1.PrimeSubsetCertificates.targets
    (anchorPrimes Y x u) (assignmentExponent t N Y) B N N (fun w ↦ w.val)

def incomingCover (t B N : ℕ) (Y : ℝ) (y : ℕ) : Finset ℕ :=
  (anchorOffsets t B).biUnion fun u ↦ PaperP1.PrimeSubsetCertificates.targets
    (receiverPrimes B Y y) (assignmentExponent t N Y) t N N (fun i ↦ (u i).val)

theorem mem_anchorOffsets (t B : ℕ) (u : Fin t → Fin B) :
    u ∈ anchorOffsets t B ↔ Function.Injective u := by
  simp only [anchorOffsets, mem_filter, mem_univ, true_and]

theorem card_anchorOffsets_le (t B : ℕ) : (anchorOffsets t B).card ≤ B ^ t := by
  calc
    _ ≤ Fintype.card (Fin t → Fin B) := card_filter_le _ _
    _ = _ := by simp only [Fintype.card_fun, Fintype.card_fin]

theorem outgoing_subset_cover {t B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    outgoing t B N Y x ⊆ outgoingCover t B N Y x := by
  classical
  intro y hy
  obtain ⟨hy, _, u, hu, D, hD, hdiv, hreceiving⟩ := (mem_outgoing t B N Y x y).mp hy
  obtain ⟨hsub, hcard, hprod, _hND, _hprimes⟩ :=
    divisor_data hN hB hBN hx Y hY u hu D hD hdiv
  let S := D.primeFactors
  have hw : ∀ p : S, ∃ w : Fin B, p.val ∣ value y w := fun p ↦ hreceiving p.val p.property
  let w : S → Fin B := fun p ↦ Classical.choose (hw p)
  have hwdiv (p : S) : p.val ∣ y - 1 + (w p).val := Classical.choose_spec (hw p)
  apply mem_biUnion.mpr
  refine ⟨u, (mem_anchorOffsets t B _).mpr hu, ?_⟩
  apply (PaperP1.PrimeSubsetCertificates.mem_targets _ _ B N N y _).mpr
  exact ⟨by simpa only [two_mul] using hy, S, hsub, hcard, by rwa [hprod], w, hwdiv⟩

theorem incoming_subset_cover {t B N y : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    incoming t B N Y y ⊆ incomingCover t B N Y y := by
  classical
  intro x hx
  obtain ⟨hx, _, u, hu, D, hD, hdiv, hreceiving⟩ := (mem_incoming t B N Y x y).mp hx
  obtain ⟨_hsub, hcard, hprod, _hND, hprimes⟩ :=
    divisor_data hN hB hBN hx Y hY u hu D hD hdiv
  let S := D.primeFactors
  have hsub : S ⊆ receiverPrimes B Y y := by
    intro p hp
    obtain ⟨w, hw⟩ := hreceiving p hp
    have hprime := hprimes p hp
    apply (mem_receiverPrimes B Y y p).mpr
    exact ⟨w, (mem_largePrimes Y _ p (value_bounds hN hBN hy w).1).mpr
      ⟨hprime.1, hw, hprime.2.1⟩⟩
  have hw : ∀ p : S, ∃ i : Fin t, p.val ∣ x - 1 + (u i).val :=
    fun p ↦ (hprimes p.val p.property).2.2
  let w : S → Fin t := fun p ↦ Classical.choose (hw p)
  have hwdiv (p : S) : p.val ∣ x - 1 + (u (w p)).val := Classical.choose_spec (hw p)
  apply mem_biUnion.mpr
  refine ⟨u, (mem_anchorOffsets t B _).mpr hu, ?_⟩
  apply (PaperP1.PrimeSubsetCertificates.mem_targets _ _ t N N x _).mpr
  exact ⟨by simpa only [two_mul] using hx, S, hsub, hcard, by rwa [hprod], w, hwdiv⟩

theorem card_outgoingCover_le {t B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoingCover t B N Y x).card : ℝ) ≤
      (B : ℝ) ^ t * ((B : ℝ) + 1) ^ assignmentExponent t N Y := by
  have hcard : ((anchorOffsets t B).card : ℝ) ≤ (B : ℝ) ^ t := by
    exact_mod_cast card_anchorOffsets_le t B
  calc
    _ ≤ ∑ u ∈ anchorOffsets t B, ((PaperP1.PrimeSubsetCertificates.targets
        (anchorPrimes Y x u) (assignmentExponent t N Y) B N N (fun w ↦ w.val)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (outgoingCover t B N Y x).card ≤ _)
    _ ≤ ∑ _u ∈ anchorOffsets t B, ((B : ℝ) + 1) ^ assignmentExponent t N Y := by
      apply sum_le_sum
      intro u hu
      obtain ⟨_hpos, _hsq, _hupper, hPcard, hP⟩ :=
        anchor_data hN hB hBN hx Y hY u ((mem_anchorOffsets t B u).mp hu)
      calc
        _ ≤ (1 + (B : ℝ)) ^ (anchorPrimes Y x u).card :=
          PaperP1.PrimeSubsetCertificates.card_targets_le_full _ (fun p hp ↦ (hP p hp).1)
            _ B N N (by omega) _
        _ ≤ _ := by
          rw [add_comm 1 (B : ℝ)]
          apply pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) B] :
            (1 : ℝ) ≤ (B : ℝ) + 1) hPcard
    _ = ((anchorOffsets t B).card : ℝ) * ((B : ℝ) + 1) ^ assignmentExponent t N Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem card_incomingCover_le {t B N y : ℕ} (ht : 1 ≤ t) (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((incomingCover t B N Y y).card : ℝ) ≤
      (B : ℝ) ^ t * ((t : ℝ) * Real.exp 1 * B) ^ assignmentExponent t N Y := by
  have hY1 : 1 < Y := by
    have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
    linarith
  have hpool := card_receiverPrimes_le (t := t) ht hN hBN hy Y hY1
  have hpoolR : ((receiverPrimes B Y y).card : ℝ) ≤ (B : ℝ) * assignmentExponent t N Y := by
    exact_mod_cast hpool
  have hcard : ((anchorOffsets t B).card : ℝ) ≤ (B : ℝ) ^ t := by
    exact_mod_cast card_anchorOffsets_le t B
  calc
    _ ≤ ∑ u ∈ anchorOffsets t B, ((PaperP1.PrimeSubsetCertificates.targets
        (receiverPrimes B Y y) (assignmentExponent t N Y) t N N (fun i ↦ (u i).val)).card : ℝ) := by
      exact_mod_cast (card_biUnion_le : (incomingCover t B N Y y).card ≤ _)
    _ ≤ ∑ _u ∈ anchorOffsets t B,
        ((t : ℝ) * Real.exp 1 * B) ^ assignmentExponent t N Y := by
      apply sum_le_sum
      intro u _
      have htarget := PaperP1.PrimeSubsetCertificates.card_targets_le _
        (receiverPrimes_prime B Y y) (assignmentExponent t N Y) t N N (by omega)
        (fun i ↦ (u i).val)
      have hw := PaperP1.BoundedSubsetWeights.weightSum_le_of_card_le
        (receiverPrimes B Y y) (t : ℝ) (B : ℝ) (assignmentExponent t N Y)
        (by exact_mod_cast ht) (by exact_mod_cast (show 1 ≤ B by omega)) hpoolR
      exact htarget.trans hw
    _ = ((anchorOffsets t B).card : ℝ) *
        ((t : ℝ) * Real.exp 1 * B) ^ assignmentExponent t N Y := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem outgoing_bound {t B N x : ℕ} (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hx : x ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((outgoing t B N Y x).card : ℝ) ≤
      (B : ℝ) ^ t * ((B : ℝ) + 1) ^ assignmentExponent t N Y := by
  have hsub : ((outgoing t B N Y x).card : ℝ) ≤ (outgoingCover t B N Y x).card := by
    exact_mod_cast card_le_card (outgoing_subset_cover hN hB hBN hx Y hY)
  exact hsub.trans (card_outgoingCover_le hN hB hBN hx Y hY)

theorem incoming_bound {t B N y : ℕ} (ht : 1 ≤ t) (hN : 10 ≤ N) (hB : 2 ≤ B)
    (hBN : B ≤ N + 1) (hy : y ∈ Ico N (2 * N)) (Y : ℝ) (hY : (B : ℝ) ≤ Y) :
    ((incoming t B N Y y).card : ℝ) ≤
      (B : ℝ) ^ t * ((t : ℝ) * Real.exp 1 * B) ^ assignmentExponent t N Y := by
  have hsub : ((incoming t B N Y y).card : ℝ) ≤ (incomingCover t B N Y y).card := by
    exact_mod_cast card_le_card (incoming_subset_cover hN hB hBN hy Y hY)
  exact hsub.trans (card_incomingCover_le ht hN hB hBN hy Y hY)

end PaperP1.MultiAnchorSaturationCounts
