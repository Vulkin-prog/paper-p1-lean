module

public import PaperP1.Asymptotics.PrefixParticipatingTail
public import PaperP1.Affine.OneSeedParticipation
public import PaperP1.Combinatorics.OneSeedWeights

/-! # One arbitrary effective source at all cardinalities

The source is contained in one complete window of the common logarithmic
width. Every collision and every distinguished-source multiplicity is kept.
The source subspace and the heterogeneous weights may vary after N and L.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixOneSeedTail

open Finset PaperP1.Arithmetic PaperP1.Model

theorem uniform_tail (D M a ε : ℝ) (hD : 1 ≤ D) (hM : 0 ≤ M) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      1 ≤ L → ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ W : ℕ → Submodule F₂ (ℕ →₀ F₂),
      (∀ x ∈ Ico 2 (N + 2), W x ≤ squareClassSpace x L) →
      ∀ p w : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x, 0 ≤ w x) →
      (∀ x ∈ Ico 2 (N + 2), p x ≤ M / N) → (∀ x ∈ Ico 2 (N + 2), w x ≤ M / N) →
      ∀ Families : ℕ → Finset (Finset ℕ),
      (∀ x ∈ Ico 2 (N + 2), ∀ I ∈ Families x,
        I ⊆ Ico 2 (N + 2) ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L (W x) I) →
      (∑ x ∈ Ico 2 (N + 2), w x * ∑ I ∈ Families x, ∏ y ∈ I, p y) ≤ (N : ℝ) ^ (-a + ε) := by
  classical
  obtain ⟨s, hs, NT, _hNT, ht⟩ := PrefixParticipatingTail.subcritical_tail D (2 * M) a (ε / 2)
    hD (by positivity) ha (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((1 + M) ^ 2) (-a + ε / 2) (ε / 2) (by positivity)
  refine ⟨s + 1, by omega, max 10 (max NT NF), by omega, ?_⟩
  intro N hN L hL hwidth W hW p w hp hw hpcap hwcap Families hF
  let G := Ico 2 (N + 2)
  let T := G.powerset.filter fun J ↦ s ≤ J.card ∧ RelativeWindowFamilies.Witnesses L ⊥ J
  let m := M / (N : ℝ)
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hm : 0 ≤ m := div_nonneg hM hn.le
  have hT : ∀ J ∈ T, J ⊆ G ∧ s ≤ J.card ∧ RelativeWindowFamilies.Witnesses L ⊥ J := by
    intro J hJ
    obtain ⟨hJG, hsize, hpart⟩ := mem_filter.mp hJ
    exact ⟨mem_powerset.mp hJG, hsize, hpart⟩
  have hcover : ∀ x ∈ G, ∀ I ∈ Families x, I ⊆ G ∧ (insert x I ∈ T ∨ I.erase x ∈ T) := by
    intro x hx I hI
    obtain ⟨hIG, hsize, hpart⟩ := hF x hx I hI
    refine ⟨hIG, ?_⟩
    have hh := OneSeedParticipation.insert_or_erase (fun y ↦ squareClassSpace y L) (W x) x I (hW x hx) hpart
    rcases hh with hi | he
    · left
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hx hIG), ?_, hi⟩
      have hc := card_le_card (subset_insert x I)
      omega
    · right
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr ((erase_subset x I).trans hIG), ?_, he⟩
      by_cases hxI : x ∈ I
      · have hc := card_erase_add_one hxI
        omega
      · rw [erase_eq_of_notMem hxI]
        omega
  have hmass := OneSeedWeights.heterogeneous_bound G T Families p w m hm hp hw hpcap hwcap
    (fun J hJ ↦ (hT J hJ).1) hcover
  have htail : (∑ J ∈ T, (2 * m) ^ J.card) ≤ (N : ℝ) ^ (-a + ε / 2) := by
    have hh := ht N (by omega) L hL hwidth (fun _ ↦ 2 * m) (fun _ ↦ by positivity)
      (fun _ _ ↦ by dsimp [m]; ring_nf; exact le_rfl) T hT
    simpa only [prod_const] using hh
  have hcard : (G.card : ℝ) = N := by simp only [G, Nat.card_Ico, Nat.add_sub_cancel]
  have hmM : m ≤ M := div_le_self hM hn1
  have hNm : (N : ℝ) * m = M := by dsimp [m]; field_simp
  have hNm₂ : (N : ℝ) * m ^ 2 = M * m := by rw [pow_two, ← mul_assoc, hNm]
  have hMm := mul_le_mul_of_nonneg_left hmM hM
  have hconstant : 1 + (G.card : ℝ) * (2 * m + m ^ 2) ≤ (1 + M) ^ 2 := by
    rw [hcard]
    nlinarith only [hNm, hNm₂, hMm]
  calc
    _ ≤ (1 + (G.card : ℝ) * (2 * m + m ^ 2)) * ∑ J ∈ T, (2 * m) ^ J.card := hmass
    _ ≤ (1 + M) ^ 2 * (N : ℝ) ^ (-a + ε / 2) :=
      mul_le_mul hconstant htail (sum_nonneg fun _ _ ↦ pow_nonneg (by positivity) _) (sq_nonneg _)
    _ ≤ (N : ℝ) ^ (-a + ε / 2 + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrefixOneSeedTail
