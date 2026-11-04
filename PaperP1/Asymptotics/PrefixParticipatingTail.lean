module

public import PaperP1.Model.PrefixWindowCertificateMass
public import PaperP1.Asymptotics.PrefixModerateCertificateAsymptotic
public import PaperP1.Asymptotics.PrefixSaturationDegrees
public import PaperP1.Asymptotics.UniformGraphCardinalityTail
public import PaperP1.Asymptotics.OriginalParticipatingTail

/-! # Positive-prefix participating families at every logarithmic width and all cardinalities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrefixParticipatingTail

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.PrefixWindowCertificateFamilies
  PaperP1.CriticalBandScale PaperP1.PrefixSaturationGraph

theorem uniform_split_bound (D M A β σ θ ε : ℝ) (hD : 1 ≤ D) (hM : 0 ≤ M) (hA : 1 < A) (hβ : 0 ≤ β)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hcut : A * (1 - σ) < 1)
    (hθ : 0 < θ) (hmarkgap : 2 * θ < (1 - β) * (1 - σ))
    (hdeggap : 2 / A < 1 - 2 * θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      1 ≤ L → ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ (Ico 2 (N + 2)), p x ≤ M / N) →
      ∀ s : ℕ, ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ (Ico 2 (N + 2)) ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-2 * β + 4 / A + ε) + (N : ℝ) ^ (-θ * s + ε) := by
  classical
  let δ := (1 - β) * (1 - σ)
  let ζ := min (δ - 2 * θ) (1 - 2 * θ - 2 / A) / 2
  have hζ : 0 < ζ := div_pos (lt_min (by dsimp [δ]; linarith only [hmarkgap])
    (by linarith only [hdeggap])) (by norm_num)
  have hzmark : 1 - δ + ζ ≤ 1 - 2 * θ := by
    have h := min_le_left (δ - 2 * θ) (1 - 2 * θ - 2 / A)
    dsimp only [ζ] at hζ ⊢
    linarith only [h, hζ]
  have hzdeg : 2 / A + ζ ≤ 1 - 2 * θ := by
    have h := min_le_right (δ - 2 * θ) (1 - 2 * θ - 2 / A)
    dsimp only [ζ] at hζ ⊢
    linarith only [h, hζ]
  obtain ⟨NM, _hNM, hm⟩ := PrefixMarkedWindowCount.uniform_count A β σ D ζ hσ hσ1 hβ (zero_le_one.trans hD) hcut hζ
  obtain ⟨ND, hd⟩ := PrefixSaturationDegrees.uniform_degrees D A ζ hD hA hζ
  obtain ⟨NF, hf⟩ := PrefixSaturationDegrees.finite_conditions D A hD hA
  obtain ⟨NC, hc⟩ := eventually_atTop.mp (PrefixModerateCertificateAsymptotic.weightedTotal_le_power_eventually
    A β D M ε hA hβ hD hε)
  obtain ⟨NG, _hNG, hg⟩ := UniformGraphCardinalityTail.uniform_tail M θ ε hM hθ hε
  refine ⟨10 + NM + ND + NF + NC + NG, by omega, ?_⟩
  intro N hN L hL hwidth p hp hcap s F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hN10, hB, hBN, hY⟩ := hf N (by omega) L hL hwidth
  let Y := ModerateOrder.cutoff A N
  let T := (N : ℝ) ^ β
  let FC := F.filter fun I ↦ Certified I.card (L + 1) N Y T I
  let FB := F.filter fun I ↦ ¬ Certified I.card (L + 1) N Y T I
  have hcertmass : (∑ I ∈ FC, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
    calc
      _ ≤ PrefixModerateWeightedSeries.weightedTotal (L + 1) N Y T (M / N) :=
        PrefixWindowCertificateMass.certified_total_bound (L + 1) N Y T FC
          (fun I hI ↦ (hF I (mem_filter.mp hI).1).1) (fun _ hI ↦ (mem_filter.mp hI).2)
          p hp (M / N) (div_nonneg hM hn.le) hcap
      _ ≤ _ := hc N (by omega) (L + 1) hB hBN hwidth (M / N)
        (div_nonneg hM hn.le) (by rw [div_mul_cancel₀ _ hn.ne'])
  let marks := vertices N (PrefixMarkedWindowCount.marked (L + 1) N Y T)
  have hmarksub : PrefixMarkedWindowCount.marked (L + 1) N Y T ⊆ (Ico 2 (N + 2)) :=
    fun _ hx ↦ ((PrefixMarkedWindowCount.mem_marked _ _ _ _ _).mp hx).1
  have hmarks : (marks.card : ℝ) ≤ (N : ℝ) ^ (1 - 2 * θ) := by
    rw [show marks.card = (PrefixMarkedWindowCount.marked (L + 1) N Y T).card from vertices_card N _ hmarksub]
    exact (hm N (by omega) L hBN hwidth).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 hzmark)
  have hdegree : ((graph (L + 1) N Y).maxDegree : ℝ) ≤ (N : ℝ) ^ (1 - 2 * θ) :=
    (hd N (by omega) L hL hwidth).2.trans (Real.rpow_le_rpow_of_exponent_le hn1 hzdeg)
  have hvertices : (Fintype.card (Vertex N) : ℝ) ≤ N := by
    simp only [Vertex, Fintype.card_coe, Nat.card_Ico, Nat.add_sub_cancel]
    exact le_rfl
  have himage : FB.image (vertices N) ⊆ GraphStarWeights.families (graph (L + 1) N Y) marks := by
    intro D hD
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hD
    obtain ⟨hIF, hnot⟩ := mem_filter.mp hI
    exact (GraphStarWeights.mem_families _ _ _).mpr
      (noncertified_admissible I (hF I hIF).1 (by omega) Y T hY (hF I hIF).2.2 hnot)
  have hcardimage : ∀ D ∈ FB.image (vertices N), s ≤ D.card := by
    intro D hD
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hD
    rw [vertices_card N I (hF I (mem_filter.mp hI).1).1]
    exact (hF I (mem_filter.mp hI).1).2.1
  have hgraphmass := hg N (by omega) (Vertex N) (graph (L + 1) N Y) hvertices marks hmarks hdegree
    s (FB.image (vertices N)) himage hcardimage
  have hvinj : Set.InjOn (vertices N) (FB : Set (Finset ℕ)) := by
    intro I hI J hJ heq
    have h := congrArg (fun D : Finset (Vertex N) ↦ D.image Subtype.val) heq
    simpa only [vertices_image N I (hF I (mem_filter.mp hI).1).1,
      vertices_image N J (hF J (mem_filter.mp hJ).1).1] using h
  have hbadmass : (∑ I ∈ FB, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-θ * s + ε) := by
    calc
      _ ≤ ∑ I ∈ FB, (M / N) ^ I.card := by
        apply sum_le_sum
        intro I hI
        have hprod : (∏ x ∈ I, p x) ≤ ∏ _x ∈ I, M / N :=
          prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦ hcap x ((hF I (mem_filter.mp hI).1).1 hx))
        simpa only [prod_const] using hprod
      _ = ∑ D ∈ FB.image (vertices N), (M / N) ^ D.card := by
        rw [sum_image hvinj]
        exact sum_congr rfl fun I hI ↦ congrArg (fun r : ℕ ↦ (M / N) ^ r)
          (vertices_card N I (hF I (mem_filter.mp hI).1).1).symm
      _ ≤ _ := hgraphmass
  calc
    _ = (∑ I ∈ FC, ∏ x ∈ I, p x) + ∑ I ∈ FB, ∏ x ∈ I, p x :=
      (sum_filter_add_sum_filter_not F (fun I ↦ Certified I.card (L + 1) N Y T I) _).symm
    _ ≤ _ := add_le_add hcertmass hbadmass

theorem subcritical_tail (D M a ε : ℝ) (hD : 1 ≤ D) (hM : 0 ≤ M) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      1 ≤ L → ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ (Ico 2 (N + 2)), p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ (Ico 2 (N + 2)) ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-a + ε) := by
  obtain ⟨A, β, σ, θ, hA, hβ, hσ, hσ1, hcut, hθ, hmarkgap, hdeggap, hmod⟩ := OriginalParticipatingTail.subcritical_parameters a ha
  obtain ⟨s, hs⟩ := exists_nat_gt (max 1 (a / θ))
  have hθs : a ≤ θ * (s : ℝ) := by
    have h := (div_lt_iff₀ hθ).mp ((le_max_right 1 (a / θ)).trans_lt hs)
    linarith only [h]
  have hsone : 1 ≤ s := by
    have h : (1 : ℝ) < s := (le_max_left 1 (a / θ)).trans_lt hs
    have hnat : 1 < s := by exact_mod_cast h
    omega
  obtain ⟨NP, _hNP, hp⟩ := uniform_split_bound D M A β σ θ (ε / 2) hD hM hA hβ hσ hσ1 hcut
    hθ hmarkgap hdeggap (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-a + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hsone, max 10 (max NP NA), by omega, ?_⟩
  intro N hN L hL hwidth p hpos hcap F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsplit := hp N (by omega) L hL hwidth p hpos hcap s F hF
  calc
    _ ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε / 2) + (N : ℝ) ^ (-θ * s + ε / 2) := hsplit
    _ ≤ (N : ℝ) ^ (-a + ε / 2) + (N : ℝ) ^ (-a + ε / 2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hmod]))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hθs]))
    _ = 2 * (N : ℝ) ^ (-a + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-a + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.PrefixParticipatingTail
