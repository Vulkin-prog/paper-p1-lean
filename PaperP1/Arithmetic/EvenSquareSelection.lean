module

public import PaperP1.Coding.RungeDefectApplication

/-! # No short even square selection of distinct integers in a narrow interval -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EvenSquareSelection

open Finset PaperP1.Arithmetic

theorem cardinal_gt {S : Finset ℕ} {U R t : ℕ} (hne : S.Nonempty)
    (heven : Even S.card) (hsquare : ∃ q : ℕ, ∏ n ∈ S, n = q ^ 2)
    (hlower : ∀ n ∈ S, U ≤ n) (hupper : ∀ n ∈ S, n ≤ U + R)
    (hR : 1 ≤ R) (hU : 2 * R ≤ U) (hgrowth : (64 * R) ^ (2 * t) < U) :
    2 * t < S.card := by
  obtain ⟨k, hk⟩ := heven
  have hcard : S.card = 2 * k := by simpa only [two_mul] using hk
  have hkpos : 1 ≤ k := by have := hne.card_pos; omega
  by_contra hnot
  have hkt : k ≤ t := by omega
  let f : S → ℕ := fun n ↦ n.val
  have hinj : Function.Injective f := fun _ _ h ↦ Subtype.ext h
  have hsquare' : ∃ q : ℕ, ∏ n : S, f n = q ^ 2 := by
    obtain ⟨q, hq⟩ := hsquare
    refine ⟨q, ?_⟩
    exact (prod_coe_sort S (fun n : ℕ ↦ n)).trans hq
  obtain ⟨hshift, hbounded, hprod⟩ := RungeTranslation.translatedRungeInput hinj
    (fun n ↦ hlower n.val n.property) (fun n ↦ hupper n.val n.property) hsquare'
  obtain ⟨γ, hγinj, hγbound, hγsquare⟩ :=
    DefectCodeDistance.reindex_translatedRungeInput f hcard hshift hbounded hprod
  exact RungeDefectApplication.noShortRungeSquare_of_endpoint_growth hR hU hgrowth
    k hkpos hkt γ hγinj hγbound hγsquare

end PaperP1.EvenSquareSelection
