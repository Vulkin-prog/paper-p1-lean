module

public import PaperP1.Model.WindowCertificateMass
public import PaperP1.Asymptotics.ModerateCertificateAsymptotic
public import PaperP1.Asymptotics.SaturationDegrees
public import PaperP1.Asymptotics.UniformGraphCardinalityTail

/-! # Original participating families at all orders: actual moderate mass plus the actual saturated cardinality tail -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalParticipatingTail

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.WindowCertificateFamilies
  PaperP1.CriticalBandScale PaperP1.SaturationGraph

theorem uniform_split_bound (C M A β σ θ ε : ℝ) (hM : 0 ≤ M) (hA : 1 < A) (hβ : 0 ≤ β)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hcut : A * (1 - σ) < 1)
    (hθ : 0 < θ) (hmarkgap : 2 * θ < (1 - β) * (1 - σ))
    (hdeggap : 2 / A < 1 - 2 * θ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ s : ℕ, ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
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
  have hD : 1 ≤ upperScale := by
    unfold upperScale
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith [one_div_pos.mpr hlog]
  obtain ⟨NM, _hNM, hm⟩ := MarkedWindowCount.uniform_count A β σ upperScale ζ hσ hσ1 hβ upperScale_pos.le hcut hζ
  obtain ⟨ND, hd⟩ := SaturationDegrees.main_7_3 C A ζ hA hζ
  obtain ⟨NF, hf⟩ := SaturationDegrees.finite_conditions C A hA
  obtain ⟨NC, hc⟩ := eventually_atTop.mp (ModerateCertificateAsymptotic.weightedTotal_le_power_eventually
    A β upperScale M ε hA hβ hD hε)
  obtain ⟨NG, _hNG, hg⟩ := UniformGraphCardinalityTail.uniform_tail M θ ε hM hθ hε
  refine ⟨10 + NM + ND + NF + NC + NG, by omega, ?_⟩
  intro N hN L hband p hp hcap s F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  obtain ⟨hN10, hB, hBN, hY, hwidth⟩ := hf N (by omega) L hband
  let Y := ModerateOrder.cutoff A N
  let T := (N : ℝ) ^ β
  let FC := F.filter fun I ↦ Certified I.card (L + 1) N Y T I
  let FB := F.filter fun I ↦ ¬ Certified I.card (L + 1) N Y T I
  have hcertmass : (∑ I ∈ FC, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε) := by
    calc
      _ ≤ ModerateWeightedSeries.weightedTotal (L + 1) N Y T (M / N) :=
        WindowCertificateMass.certified_total_bound (L + 1) N Y T FC
          (fun I hI ↦ (hF I (mem_filter.mp hI).1).1) (fun _ hI ↦ (mem_filter.mp hI).2)
          p hp (M / N) (div_nonneg hM hn.le) hcap
      _ ≤ _ := hc N (by omega) (L + 1) hB hBN hwidth (M / N)
        (div_nonneg hM hn.le) (by rw [div_mul_cancel₀ _ hn.ne'])
  let marks := vertices N (MarkedWindowCount.marked (L + 1) N Y T)
  have hmarksub : MarkedWindowCount.marked (L + 1) N Y T ⊆ dyadicBlock N :=
    fun _ hx ↦ ((MarkedWindowCount.mem_marked _ _ _ _ _).mp hx).1
  have hmarks : (marks.card : ℝ) ≤ (N : ℝ) ^ (1 - 2 * θ) := by
    rw [show marks.card = (MarkedWindowCount.marked (L + 1) N Y T).card from vertices_card N _ hmarksub]
    exact (hm N (by omega) L hBN hwidth).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 hzmark)
  have hdegree : ((graph (L + 1) N Y).maxDegree : ℝ) ≤ (N : ℝ) ^ (1 - 2 * θ) :=
    (hd N (by omega) L hband).2.trans (Real.rpow_le_rpow_of_exponent_le hn1 hzdeg)
  have hvertices : (Fintype.card (Vertex N) : ℝ) ≤ N := by
    simp only [Vertex, Fintype.card_coe, Nat.card_Ico]
    norm_cast
    omega
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

theorem subcritical_parameters (a : ℝ) (ha : a < 2) :
    ∃ A β σ θ : ℝ, 1 < A ∧ 0 ≤ β ∧ 1 / 2 ≤ σ ∧ σ < 1 ∧ A * (1 - σ) < 1 ∧
      0 < θ ∧ 2 * θ < (1 - β) * (1 - σ) ∧ 2 / A < 1 - 2 * θ ∧ -2 * β + 4 / A ≤ -a := by
  let a₀ := max 0 a
  let d := 2 - a₀
  have ha₀ : 0 ≤ a₀ := le_max_left _ _
  have ha₀two : a₀ < 2 := max_lt (by norm_num) ha
  have haa : a ≤ a₀ := le_max_right _ _
  have hd : 0 < d := by dsimp [d]; linarith only [ha₀two]
  have hd2 : d ≤ 2 := by dsimp [d]; linarith only [ha₀]
  let A := 32 / d
  let β := (a₀ + 2) / 4
  let q := d / 64
  let σ := 1 - q
  let δ := (1 - β) * q
  let θ := δ / 4
  have hA16 : 16 ≤ A := (le_div_iff₀ hd).mpr (by linarith only [hd2])
  have hApos : 0 < A := by linarith only [hA16]
  have hβ : 0 ≤ β := by dsimp [β]; linarith only [ha₀]
  have hβ1 : β < 1 := by dsimp [β]; linarith only [ha₀two]
  have hq : 0 < q := div_pos hd (by norm_num)
  have hq32 : q ≤ 1 / 32 := by dsimp [q]; linarith only [hd2]
  have hδ : 0 < δ := mul_pos (by linarith only [hβ1]) hq
  have hδ32 : δ ≤ 1 / 32 := by
    have hle : δ ≤ q := by dsimp [δ]; nlinarith only [hβ, hq]
    exact hle.trans hq32
  have hθ : 0 < θ := div_pos hδ (by norm_num)
  have hθ128 : θ ≤ 1 / 128 := by dsimp [θ]; linarith only [hδ32]
  have hfour : 4 / A = d / 8 := by dsimp [A]; field_simp; norm_num
  have htwo : 2 / A ≤ 1 / 8 := (div_le_iff₀ hApos).mpr (by linarith only [hA16])
  have hcut : A * (1 - σ) = 1 / 2 := by dsimp [A, σ, q]; field_simp; ring
  refine ⟨A, β, σ, θ, by linarith only [hA16], hβ, ?_, ?_, by rw [hcut]; norm_num, hθ, ?_, ?_, ?_⟩
  · dsimp [σ]
    linarith only [hq32]
  · dsimp [σ]
    linarith only [hq]
  · change 2 * (δ / 4) < (1 - β) * (1 - (1 - q))
    have heq : (1 - β) * (1 - (1 - q)) = δ := by dsimp [δ]; ring
    rw [heq]
    linarith only [hδ]
  · linarith only [htwo, hθ128]
  · rw [hfour]
    dsimp [β, d]
    linarith only [haa, ha₀two]

theorem subcritical_tail (C M a ε : ℝ) (hM : 0 ≤ M) (ha : a < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧ RelativeWindowFamilies.Witnesses L ⊥ I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤ (N : ℝ) ^ (-a + ε) := by
  obtain ⟨A, β, σ, θ, hA, hβ, hσ, hσ1, hcut, hθ, hmarkgap, hdeggap, hmod⟩ := subcritical_parameters a ha
  obtain ⟨s, hs⟩ := exists_nat_gt (max 1 (a / θ))
  have hθs : a ≤ θ * (s : ℝ) := by
    have h := (div_lt_iff₀ hθ).mp ((le_max_right 1 (a / θ)).trans_lt hs)
    linarith only [h]
  have hsone : 1 ≤ s := by
    have h : (1 : ℝ) < s := (le_max_left 1 (a / θ)).trans_lt hs
    have hnat : 1 < s := by exact_mod_cast h
    omega
  obtain ⟨NP, _hNP, hp⟩ := uniform_split_bound C M A β σ θ (ε / 2) hM hA hβ hσ hσ1 hcut
    hθ hmarkgap hdeggap (by positivity)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 2 (-a + ε / 2) (ε / 2) (by positivity)
  refine ⟨s, hsone, max 10 (max NP NA), by omega, ?_⟩
  intro N hN L hband p hpos hcap F hF
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsplit := hp N (by omega) L hband p hpos hcap s F hF
  calc
    _ ≤ (N : ℝ) ^ (-2 * β + 4 / A + ε / 2) + (N : ℝ) ^ (-θ * s + ε / 2) := hsplit
    _ ≤ (N : ℝ) ^ (-a + ε / 2) + (N : ℝ) ^ (-a + ε / 2) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hmod]))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hθs]))
    _ = 2 * (N : ℝ) ^ (-a + ε / 2) := by ring
    _ ≤ (N : ℝ) ^ ((-a + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.OriginalParticipatingTail
