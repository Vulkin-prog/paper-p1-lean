module

public import PaperP1.Asymptotics.GeneralGraphHostCount
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # The actual dense weighted two-window sector under explicit geometric inputs

The source cover, the ordinary covers for sizes two and three, and the generic
uniform curve-count properties are explicit unproved arguments. All arithmetic
graph populations, rank weights and the finite sum are constructed internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DenseWeightedSectorUnderInputs

open Finset PaperP1.LargePrimeGraphResolution PaperP1.RawPairRelationRank

theorem weighted_card_bound {α : Type*} (U : Finset α) (w : α → ℝ)
    (X A a b : ℝ) (hX : 0 < X) (hcard : (U.card : ℝ) ≤ A * X ^ a)
    (hw : ∀ x ∈ U, w x ≤ X ^ b) :
    (∑ x ∈ U, w x) ≤ A * X ^ (a + b) := by
  calc
    _ ≤ ∑ _x ∈ U, X ^ b := sum_le_sum hw
    _ = (U.card : ℝ) * X ^ b := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (A * X ^ a) * X ^ b := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hX.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hX]

theorem relative_kernel_le_full_sum (F : Finset (ℕ × ℕ)) (L : ℕ) :
    (∑ p ∈ F, ((2 ^ Model.InfiniteStarts.runRelativeNullity L {p.1, p.2} : ℝ) - 1)) ≤
      ∑ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ) := by
  apply sum_le_sum
  intro p _hp
  have hpow : (2 ^ Model.InfiniteStarts.runRelativeNullity L {p.1, p.2} : ℝ) ≤
      (2 ^ fullRank p.1 p.2 L : ℝ) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (relative_le_full p.1 p.2 L)
  linarith

theorem full_kernel_le_full_sum (F : Finset (ℕ × ℕ)) (L : ℕ) :
    (∑ p ∈ F, ((2 ^ fullRank p.1 p.2 L : ℝ) - 1)) ≤
      ∑ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ) := by
  apply sum_le_sum
  intro p _hp
  linarith

theorem uniform_full_weight (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap η) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        (∑ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ)) ≤ A * (N : ℝ) ^ (1 + ε)) := by
  let δ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨Ds, k, hDs, hdense⟩ := GeneralGraphHostCount.uniform_dense_hosts C δ η hδ hη
  obtain ⟨k₁, htwo⟩ := DegreeOneGraphHostCount.uniform_hosts C δ 1 (by decide) hδ
  obtain ⟨k₂, hthree⟩ := DegreeOneGraphHostCount.uniform_either_orientation C δ 2 (by decide) hδ
  obtain ⟨Ng, hglobal⟩ := CriticalPairKernelPowers.uniform_global C δ hδ
  obtain ⟨Ns, hsmall⟩ := CriticalPairKernelPowers.uniform_few_small C δ k₁ k₂ hδ
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨Ad, hAd, Nd, hcountd⟩ := hdense hCover hPila
  obtain ⟨A₁, hA₁, N₁, hcount₁⟩ := htwo hCover₁
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization k₁ M (hPila₁ M))
  obtain ⟨A₂, hA₂, N₂, hcount₂⟩ := hthree hCover₂
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization k₂ M (hPila₂ M))
  refine ⟨A₁ + A₂ + Ad, by positivity, max 2 (max Nd (max N₁ (max N₂ (max Ng Ns)))), ?_⟩
  intro N hN L hcrit F hdyadic hnon hdensity
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let S := F.filter fun p ↦ k₁ ≤ (DegreeOneGraphHostCount.components p.1 p.2 L 1).card
  let T := (F \ S).filter fun p ↦ k₂ ≤ (DegreeOneGraphHostCount.components p.1 p.2 L 2).card ∨
    k₂ ≤ (DegreeOneGraphHostCount.components p.2 p.1 L 2).card
  let R := (F \ S) \ T
  have hSF : S ⊆ F := filter_subset _ _
  have hTF : T ⊆ F := (filter_subset _ _).trans sdiff_subset
  have hRF : R ⊆ F := sdiff_subset.trans sdiff_subset
  have hS : (S.card : ℝ) ≤ A₁ * (N : ℝ) ^ δ :=
    hcount₁ N (by omega) L hcrit S (fun p hp ↦ hdyadic p (hSF hp))
      (fun p hp _ ↦ hnon p (hSF hp)) (fun _ hp ↦ (mem_filter.mp hp).2)
  have hT : (T.card : ℝ) ≤ A₂ * (N : ℝ) ^ δ :=
    hcount₂ N (by omega) L hcrit T (fun p hp ↦ hdyadic p (hTF hp))
      (fun _ _ h ↦ by omega) (fun _ hp ↦ (mem_filter.mp hp).2)
  have hR : (R.card : ℝ) ≤ Ad * (N : ℝ) ^ (1 / 2 + δ) :=
    hcountd N (by omega) L hcrit R (fun p hp ↦ hdyadic p (hRF hp))
      (fun p hp ↦ hnon p (hRF hp)) (fun p hp ↦ hdensity p (hRF hp))
  have hweight : ∀ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ) ≤ (N : ℝ) ^ (1 + δ) := by
    intro p hp
    exact hglobal N (by omega) L hcrit p.1 (hdyadic p hp).1 p.2 (hdyadic p hp).2
  have hweightR : ∀ p ∈ R, (2 ^ fullRank p.1 p.2 L : ℝ) ≤ (N : ℝ) ^ (1 / 2 + δ) := by
    intro p hp
    obtain ⟨hpFS, hpT⟩ := mem_sdiff.mp hp
    obtain ⟨hpF, hpS⟩ := mem_sdiff.mp hpFS
    have h₁ : (DegreeOneGraphHostCount.components p.1 p.2 L 1).card ≤ k₁ := by
      by_contra hn
      exact hpS (mem_filter.mpr ⟨hpF, by omega⟩)
    have h₂ : (DegreeOneGraphHostCount.components p.1 p.2 L 2).card ≤ k₂ := by
      by_contra hn
      exact hpT (mem_filter.mpr ⟨hpFS, Or.inl (by omega)⟩)
    have h₂' : (DegreeOneGraphHostCount.components p.2 p.1 L 2).card ≤ k₂ := by
      by_contra hn
      exact hpT (mem_filter.mpr ⟨hpFS, Or.inr (by omega)⟩)
    exact hsmall N (by omega) L hcrit p.1 (hdyadic p hpF).1 p.2 (hdyadic p hpF).2 h₁ h₂ h₂'
  have hsumS := weighted_card_bound S (fun p ↦ (2 ^ fullRank p.1 p.2 L : ℝ))
    (N : ℝ) A₁ δ (1 + δ) hNpos hS (fun p hp ↦ hweight p (hSF hp))
  have hsumT := weighted_card_bound T (fun p ↦ (2 ^ fullRank p.1 p.2 L : ℝ))
    (N : ℝ) A₂ δ (1 + δ) hNpos hT (fun p hp ↦ hweight p (hTF hp))
  have hsumR := weighted_card_bound R (fun p ↦ (2 ^ fullRank p.1 p.2 L : ℝ))
    (N : ℝ) Ad (1 / 2 + δ) (1 / 2 + δ) hNpos hR hweightR
  have hpart₁ := sum_sdiff (f := fun p : ℕ × ℕ ↦ (2 ^ fullRank p.1 p.2 L : ℝ)) hSF
  have hpart₂ := sum_sdiff (f := fun p : ℕ × ℕ ↦ (2 ^ fullRank p.1 p.2 L : ℝ))
    (show T ⊆ F \ S from filter_subset _ _)
  change (∑ p ∈ F \ S, (2 ^ fullRank p.1 p.2 L : ℝ)) + (∑ p ∈ S, (2 ^ fullRank p.1 p.2 L : ℝ)) = _ at hpart₁
  change (∑ p ∈ R, (2 ^ fullRank p.1 p.2 L : ℝ)) + (∑ p ∈ T, (2 ^ fullRank p.1 p.2 L : ℝ)) = _ at hpart₂
  have he₁ : δ + (1 + δ) = 1 + ε / 2 := by dsimp [δ]; ring
  have he₂ : (1 / 2 + δ) + (1 / 2 + δ) = 1 + ε / 2 := by dsimp [δ]; ring
  rw [he₁] at hsumS hsumT
  rw [he₂] at hsumR
  have htotal : (∑ p ∈ F, (2 ^ fullRank p.1 p.2 L : ℝ)) ≤
      (A₁ + A₂ + Ad) * (N : ℝ) ^ (1 + ε / 2) := by linarith only [hpart₁, hpart₂, hsumS, hsumT, hsumR]
  exact htotal.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)) (by positivity))

theorem uniform_kernels (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k k₁ k₂ : ℕ, 0 < Ds ∧
      (UniformSourceSurfaceCover.UniformCover k (GeneralGraphHostCount.sizeCap η) Ds →
      UniformOrdinarySurfaceCover.UniformCover k₁ 2 →
      UniformOrdinarySurfaceCover.UniformCover k₂ 3 →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₁ + 3) M) →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k₂ + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        ((∑ p ∈ F, ((2 ^ fullRank p.1 p.2 L : ℝ) - 1)) ≤ A * (N : ℝ) ^ (1 + ε) ∧
        (∑ p ∈ F, ((2 ^ Model.InfiniteStarts.runRelativeNullity L {p.1, p.2} : ℝ) - 1)) ≤
          A * (N : ℝ) ^ (1 + ε))) := by
  obtain ⟨Ds, k, k₁, k₂, hDs, hbound⟩ := uniform_full_weight C ε η hε hη
  refine ⟨Ds, k, k₁, k₂, hDs, ?_⟩
  intro hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  obtain ⟨A, hA, N₀, hcount⟩ := hbound hCover hCover₁ hCover₂ hPila hPila₁ hPila₂
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L hcrit F hdyadic hnon hdensity
  have hc := hcount N hN L hcrit F hdyadic hnon hdensity
  exact ⟨(full_kernel_le_full_sum F L).trans hc, (relative_kernel_le_full_sum F L).trans hc⟩

end PaperP1.DenseWeightedSectorUnderInputs
