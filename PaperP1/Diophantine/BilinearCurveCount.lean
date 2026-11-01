module

public import PaperP1.Diophantine.BilinearAuxiliary

/-! # The minimum of both box heights for an irreducible (1,1) auxiliary factor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BilinearCurveCount

open Finset MvPolynomial PaperP1.BilinearAuxiliary
open PaperP1.BidegreeOneFibreCount PaperP1.ProjectiveCurveCount

theorem solutions_swap {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (hC : ∀ i, (C i).IsHomogeneous k) (a b c e h : ℤ) (A H : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) :
    (realSolutions C (form a b) (form c e) h A H).image Prod.swap =
      realSolutions (PaperP1.BihomogeneousSwap.coefficients (k := k) C)
        (form a c) (form b e) h H A := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
    obtain ⟨htA, htH, htgood⟩ := (mem_realSolutions C _ _ h A H hA hH t).mp ht
    apply (mem_realSolutions _ _ _ h H A hH hA t.swap).mpr
    exact ⟨htH, htA, (good_swap C hC a b c e h t).mp htgood⟩
  · intro hs
    obtain ⟨hsH, hsA, hsgood⟩ := (mem_realSolutions _ _ _ h H A hH hA s).mp hs
    apply mem_image.mpr
    refine ⟨s.swap, ?_, by simp⟩
    apply (mem_realSolutions C _ _ h A H hA hH s.swap).mpr
    refine ⟨hsA, hsH, ?_⟩
    apply (good_swap C hC a b c e h s.swap).mpr
    simpa only [Prod.swap_swap] using hsgood

theorem solutions_swap_card {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (hC : ∀ i, (C i).IsHomogeneous k) (a b c e h : ℤ) (A H : ℝ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) :
    (realSolutions C (form a b) (form c e) h A H).card =
      (realSolutions (PaperP1.BihomogeneousSwap.coefficients (k := k) C)
        (form a c) (form b e) h H A).card := by
  rw [← solutions_swap C hC a b c e h A H hA hH]
  exact (card_image_of_injective _ Prod.swap_injective).symm

theorem actual_minimum_height_count (ell k : ℕ) (A₀ : ℝ) (hdegree : 0 < k + ell)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a b c e : ℤ,
      Irreducible (auxiliary
        (MvPolynomial.map (Int.castRingHom ℚ) (form a b))
        (MvPolynomial.map (Int.castRingHom ℚ) (form c e))) →
      (a.natAbs : ℝ) ≤ (N : ℝ) ^ A₀ → (b.natAbs : ℝ) ≤ (N : ℝ) ^ A₀ →
      (c.natAbs : ℝ) ≤ (N : ℝ) ^ A₀ → (e.natAbs : ℝ) ≤ (N : ℝ) ^ A₀ →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 1 ≤ A → 1 ≤ H →
            ((realSolutions C (form a b) (form c e) h A H).card : ℝ) ≤
              (N : ℝ) ^ ε * min A H := by
  obtain ⟨Nleft, hleft⟩ := irreducible_auxiliary_count ell k 1 A₀ (by omega)
    (by simpa only [one_mul] using hdegree) ε hε
  obtain ⟨Nright, hright⟩ := irreducible_auxiliary_count k ell 1 A₀ (by omega)
    (by simpa only [one_mul, Nat.add_comm] using hdegree) ε hε
  refine ⟨max Nleft Nright, ?_⟩
  intro N hN a b c e hirr ha hb hc he C hC h hh A H hA hH
  have hpow : 0 ≤ (N : ℝ) ^ A₀ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hboundH := hleft N (by omega) (form a b) (form c e)
    (form_homogeneous a b) (form_homogeneous c e) hirr
    (form_coefficient_bound a b _ hpow ha hb) (form_coefficient_bound c e _ hpow hc he)
    C hC h hh A H (by linarith) hH
  have hirr' : Irreducible (auxiliary
      (MvPolynomial.map (Int.castRingHom ℚ) (form a c))
      (MvPolynomial.map (Int.castRingHom ℚ) (form b e))) := by
    simp only [form_map] at hirr ⊢
    exact irreducible_transpose _ _ _ _ hirr
  have hboundA := hright N (by omega) (form a c) (form b e)
    (form_homogeneous a c) (form_homogeneous b e) hirr'
    (form_coefficient_bound a c _ hpow ha hc) (form_coefficient_bound b e _ hpow hb he)
    (PaperP1.BihomogeneousSwap.coefficients (k := k) C)
    (PaperP1.BihomogeneousSwap.coefficients_homogeneous C) h hh H A (by linarith) hA
  rw [← solutions_swap_card C hC a b c e h A H (by linarith) (by linarith)] at hboundA
  rcases le_total A H with hAH | hHA
  · simpa only [min_eq_left hAH] using hboundA
  · simpa only [min_eq_right hHA] using hboundH

theorem actual_homogeneous_minimum_height_count (ell k : ℕ) (A₀ : ℝ)
    (hdegree : 0 < k + ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F G : MvPolynomial (Fin 2) ℤ,
      F.IsHomogeneous 1 → G.IsHomogeneous 1 →
      Irreducible (auxiliary (MvPolynomial.map (Int.castRingHom ℚ) F)
        (MvPolynomial.map (Int.castRingHom ℚ) G)) →
      (∀ m, ((F.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ m, ((G.coeff m).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 1 ≤ A → 1 ≤ H →
            ((realSolutions C F G h A H).card : ℝ) ≤ (N : ℝ) ^ ε * min A H := by
  obtain ⟨N₀, hN₀⟩ := actual_minimum_height_count ell k A₀ hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN F G hF hG hirr hfc hgc C hC h hh A H hA hH
  let a := (PaperP1.HomogeneousCharts.chart F).coeff 1
  let b := (PaperP1.HomogeneousCharts.chart F).coeff 0
  let c := (PaperP1.HomogeneousCharts.chart G).coeff 1
  let e := (PaperP1.HomogeneousCharts.chart G).coeff 0
  have hF' : F = form a b := homogeneous_linear_form F hF
  have hG' : G = form c e := homogeneous_linear_form G hG
  have hpow : 0 ≤ (N : ℝ) ^ A₀ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hf := PaperP1.HomogeneousCharts.chart_coefficient_bound F hF _ hpow hfc
  have hg := PaperP1.HomogeneousCharts.chart_coefficient_bound G hG _ hpow hgc
  have hi : Irreducible (auxiliary (MvPolynomial.map (Int.castRingHom ℚ) (form a b))
      (MvPolynomial.map (Int.castRingHom ℚ) (form c e))) := by
    rw [← hF', ← hG']
    exact hirr
  have hb := hN₀ N hN a b c e hi (hf 1) (hf 0) (hg 1) (hg 0) C hC h hh A H hA hH
  simpa only [← hF', ← hG'] using hb

end PaperP1.BilinearCurveCount
