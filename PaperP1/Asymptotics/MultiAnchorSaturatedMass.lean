module

public import PaperP1.Asymptotics.UniformGraphExponentTail
public import PaperP1.Asymptotics.MultiAnchorSaturationDegrees
public import PaperP1.Model.MultiAnchorRelationFamilies

/-! # The literal saturated t-anchor tail with the exact delta/2 tilt -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiAnchorSaturatedMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.MultiAnchorGraph
open PaperP1.WindowCertificateFamilies (vertices vertices_card vertices_image)

def Saturated (t B N : ℕ) (Y T : ℝ) (I : Finset ℕ) : Prop :=
  PaperP1.GraphStarPartition.Admissible (graph t B N Y)
    (vertices N (PaperP1.MarkedWindowCount.marked B N Y T)) (vertices N I)

theorem uniform_bound (t : ℕ) (C M A β σ ε : ℝ) (ht : 1 ≤ t) (hM : 0 ≤ M)
    (hA : 1 < A) (hβ : 0 ≤ β) (hβ1 : β < 1) (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1)
    (hcut : A * (1 - σ) < 1) (hgap : (t : ℝ) / A + (1 - β) * (1 - σ) < 1)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p : ℕ → ℝ, (∀ x, 0 ≤ p x) → (∀ x ∈ dyadicBlock N, p x ≤ M / N) →
      ∀ s : ℕ, ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ s ≤ I.card ∧
        Saturated t (L + 1) N ((Real.log N) ^ A) ((N : ℝ) ^ β) I) →
      (∑ I ∈ F, ∏ x ∈ I, p x) ≤
        (N : ℝ) ^ (-(1 - β) * (1 - σ) / 2 * s + ε) := by
  classical
  let δ := (1 - β) * (1 - σ)
  let θ := (t : ℝ) / A
  let η := min (δ / 4) ((1 - θ - δ) / 2)
  have hδ : 0 < δ := mul_pos (by linarith only [hβ1]) (by linarith only [hσ1])
  have hη : 0 < η := lt_min (by positivity)
    (by dsimp [θ, δ]; linarith only [hgap])
  have hmarkgap : (1 - δ + η) + δ / 2 ≤ 1 := by
    have h := min_le_left (δ / 4) ((1 - θ - δ) / 2)
    change η ≤ δ / 4 at h
    linarith only [h, hδ]
  have hstargap : (θ + η) + 2 * (δ / 2) < 1 := by
    have h := min_le_right (δ / 4) ((1 - θ - δ) / 2)
    change η ≤ (1 - θ - δ) / 2 at h
    have hg : θ + δ < 1 := hgap
    linarith only [h, hg]
  obtain ⟨NM, _hNM, hm⟩ := PaperP1.MarkedWindowCount.uniform_count
    A β σ PaperP1.CriticalBandScale.upperScale η hσ hσ1 hβ
    PaperP1.CriticalBandScale.upperScale_pos.le hcut hη
  obtain ⟨ND, hd⟩ := PaperP1.MultiAnchorSaturationDegrees.uniform_degrees t C A η ht hA hη
  obtain ⟨NF, hf⟩ := PaperP1.SaturationDegrees.finite_conditions C A hA
  obtain ⟨NG, _hNG, hg⟩ := PaperP1.UniformGraphExponentTail.uniform_tail
    M (1 - δ + η) (θ + η) (δ / 2) ε hM (by positivity) hmarkgap hstargap hε
  refine ⟨10 + NM + ND + NF + NG, by omega, ?_⟩
  intro N hN L hband p hp hcap s F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨_hN10, _hB, hBN, _hY, hwidth⟩ := hf N (by omega) L hband
  let Y := (Real.log N) ^ A
  let T := (N : ℝ) ^ β
  let marks := vertices N (PaperP1.MarkedWindowCount.marked (L + 1) N Y T)
  have hmarksub : PaperP1.MarkedWindowCount.marked (L + 1) N Y T ⊆ dyadicBlock N :=
    fun _ hx ↦ ((PaperP1.MarkedWindowCount.mem_marked _ _ _ _ _).mp hx).1
  have hmarks : (marks.card : ℝ) ≤ (N : ℝ) ^ (1 - δ + η) := by
    rw [show marks.card = (PaperP1.MarkedWindowCount.marked (L + 1) N Y T).card from
      vertices_card N _ hmarksub]
    exact hm N (by omega) L hBN hwidth
  have hdegree : ((graph t (L + 1) N Y).maxDegree : ℝ) ≤ (N : ℝ) ^ (θ + η) :=
    (hd N (by omega) L hband).2
  have hvertices : (Fintype.card (Vertex N) : ℝ) ≤ N := by
    simp only [Vertex, Fintype.card_coe, Nat.card_Ico]
    norm_cast
    omega
  have himage : F.image (vertices N) ⊆
      PaperP1.GraphStarWeights.families (graph t (L + 1) N Y) marks := by
    intro D hD
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hD
    exact (PaperP1.GraphStarWeights.mem_families _ _ _).mpr (hF I hI).2.2
  have hcardimage : ∀ D ∈ F.image (vertices N), s ≤ D.card := by
    intro D hD
    obtain ⟨I, hI, rfl⟩ := mem_image.mp hD
    rw [vertices_card N I (hF I hI).1]
    exact (hF I hI).2.1
  have hgraphmass := hg N (by omega) (Vertex N) (graph t (L + 1) N Y) hvertices
    marks hmarks hdegree s (F.image (vertices N)) himage hcardimage
  have hvinj : Set.InjOn (vertices N) (F : Set (Finset ℕ)) := by
    intro I hI J hJ heq
    have h := congrArg (fun D : Finset (Vertex N) ↦ D.image Subtype.val) heq
    simpa only [vertices_image N I (hF I hI).1, vertices_image N J (hF J hJ).1] using h
  calc
    _ ≤ ∑ I ∈ F, (M / N) ^ I.card := by
      apply sum_le_sum
      intro I hI
      have hprod : (∏ x ∈ I, p x) ≤ ∏ _x ∈ I, M / N :=
        prod_le_prod₀ (fun x _ ↦ hp x) (fun x hx ↦ hcap x ((hF I hI).1 hx))
      simpa only [prod_const] using hprod
    _ = ∑ D ∈ F.image (vertices N), (M / N) ^ D.card := by
      rw [sum_image hvinj]
      exact sum_congr rfl fun I hI ↦ congrArg (fun r : ℕ ↦ (M / N) ^ r)
        (vertices_card N I (hF I hI).1).symm
    _ ≤ (N : ℝ) ^ (-(δ / 2) * s + ε) := hgraphmass
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.MultiAnchorSaturatedMass
