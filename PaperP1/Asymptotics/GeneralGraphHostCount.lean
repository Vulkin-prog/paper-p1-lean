module

public import PaperP1.Asymptotics.GeneralTwoBlockComponentHostData

/-! # The actual general unpinned component graph consequence under two geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralGraphHostCount

open Finset PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.LargePrimeGraphResolution
  PaperP1.TwoBlockComponentSquares PaperP1.TwoBlockComponentPatterns PaperP1.GeneralSplitRadicalPatternPool
  PaperP1.SplitRadicalPointHeight

local instance (x y L : ℕ) : DecidableRel (largePrimeGraph x y L).Adj := Classical.decRel _

def components (x y L K : ℕ) : Finset (largePrimeGraph x y L).ConnectedComponent :=
  MediumPrimeColumns.smallComponents x y L
    (nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) K

theorem mem_components (x y L K : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    c ∈ components x y L K ↔
      c ∈ nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L) ∧
      (vertices x y L c).card ≤ K := by
  classical
  exact mem_filter

theorem exists_system_of_components (k K x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hcount : k ≤ (components x y L K).card) :
    ∃ q ∈ pool k L (10 * (L + 1)) K, SmoothGeneralNonalignedHostCount.Valid K q ∧
      ∃ w : Fin k → ℤ, ∀ i,
        w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) (x : ℤ) * integerProduct (q.1.2 i) (y : ℤ) := by
  classical
  let U := components x y L K
  let e : U ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let f : Fin k → U := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph x y L).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ h ↦ hf (Subtype.ext h)
  have hdata (i) := (mem_components x y L K (c i)).mp (f i).property
  exact GeneralTwoBlockComponentHostData.exists_pattern k K x y L hx hy c hc
    (fun i ↦ (hdata i).1) (fun i ↦ (hdata i).2)

theorem uniform_hosts (C ε : ℝ) (K : ℕ) (hε : 0 < ε) :
    ∃ Ds k : ℕ, 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k K Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, k ≤ (components p.1 p.2 L K).card) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := SmoothGeneralNonalignedHostCount.uniform_hosts C ε 10 K hε
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, max 2 Nc, ?_⟩
  intro N hN L hcrit F hdyadic hnon hcomponents
  classical
  let castHost : ℕ × ℕ → ℤ × ℤ := fun p ↦ ((p.1 : ℤ), (p.2 : ℤ))
  let U := F.image castHost
  have hinj : Function.Injective castHost := by
    intro p q hpq
    change ((p.1 : ℤ), (p.2 : ℤ)) = ((q.1 : ℤ), (q.2 : ℤ)) at hpq
    apply Prod.ext
    · have hx := congrArg Prod.fst hpq
      change (p.1 : ℤ) = (q.1 : ℤ) at hx
      exact_mod_cast hx
    · have hy := congrArg Prod.snd hpq
      change (p.2 : ℤ) = (q.2 : ℤ) at hy
      exact_mod_cast hy
  have hcard : U.card = F.card := card_image_of_injective F hinj
  have hdyadic' : ∀ p ∈ U,
      (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    obtain ⟨hx, hy⟩ := hdyadic q hq
    obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp hx
    obtain ⟨hylo, hyhi⟩ := mem_Ico.mp hy
    have hxZ : (N : ℤ) ≤ (q.1 : ℤ) := by exact_mod_cast hxlo
    have hyZ : (N : ℤ) ≤ (q.2 : ℤ) := by exact_mod_cast hylo
    exact ⟨hxZ, hyZ, hxhi.le, hyhi.le⟩
  have hnon' : ∀ p ∈ U, ¬ CompressedTargetAlignment.Aligned 1 p.1.natAbs p.2.natAbs L := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact hnon q hq
  have hsystems : ∀ p ∈ U, ∃ q ∈ pool k L (10 * (L + 1)) K,
      SmoothGeneralNonalignedHostCount.Valid K q ∧ ∃ w : Fin k → ℤ,
        ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    have hx : 2 ≤ q.1 := by have h := (mem_Ico.mp (hdyadic q hq).1).1; omega
    have hy : 2 ≤ q.2 := by have h := (mem_Ico.mp (hdyadic q hq).2).1; omega
    exact exists_system_of_components k K q.1 q.2 L hx hy (hcomponents q hq)
  have hbound := hcount N (by omega) L (10 * (L + 1)) hcrit le_rfl U hdyadic' hnon' hsystems
  simpa only [hcard] using hbound

def sizeCap (η : ℝ) : ℕ := ⌈4 / η⌉₊

theorem small_density (η : ℝ) (hη : 0 < η) (x y L : ℕ)
    (hdense : η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount x y L) :
    (η / 2) * ((L + 1 : ℕ) : ℝ) ≤ ((components x y L (sizeCap η)).card : ℝ) := by
  have hceil : 4 / η ≤ (sizeCap η : ℝ) := Nat.le_ceil _
  have hprod : (4 : ℝ) ≤ (sizeCap η : ℝ) * η := (div_le_iff₀ hη).mp hceil
  have hcap : (0 : ℝ) < ((sizeCap η + 1 : ℕ) : ℝ) := by positivity
  have hratio : 2 / ((sizeCap η + 1 : ℕ) : ℝ) ≤ η / 2 := by
    apply (div_le_iff₀ hcap).mpr
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hcost : 2 * ((L + 1 : ℕ) : ℝ) / ((sizeCap η + 1 : ℕ) : ℝ) ≤
      (η / 2) * ((L + 1 : ℕ) : ℝ) := by
    calc
      _ = (2 / ((sizeCap η + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
  have hs := MediumPrimeColumns.small_component_card_real x y L
    (nontrivialUnpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)) (sizeCap η)
  change (nontrivialComponentCount x y L : ℝ) -
    2 * ((L + 1 : ℕ) : ℝ) / ((sizeCap η + 1 : ℕ) : ℝ) ≤
      ((components x y L (sizeCap η)).card : ℝ) at hs
  linarith

/-- The source's first graph consequence, including overlapping physical windows. -/
theorem uniform_dense_hosts (C ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ Ds k : ℕ, 0 < Ds ∧ (UniformSourceSurfaceCover.UniformCover k (sizeCap η) Ds →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((Ds + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ nontrivialComponentCount p.1 p.2 L) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨Ds, k, hDs, hk⟩ := uniform_hosts C ε (sizeCap η) hε
  obtain ⟨Ns, hs⟩ := CriticalBandScale.critical_band_scale C
  obtain ⟨Nl, hl⟩ := ElementaryLogGrowth.log_ge_eventually
    (2 * (k : ℝ) / (η * CriticalBandScale.lowerScale))
  refine ⟨Ds, k, hDs, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc (max Ns Nl), ?_⟩
  intro N hN L hcrit F hdyadic hnon hdense
  have hscale := (hs N (by omega) L hcrit).1
  have hlog := (div_le_iff₀ (mul_pos hη CriticalBandScale.lowerScale_pos)).mp (hl N (by omega)).1
  have hscaled := mul_le_mul_of_nonneg_left hscale hη.le
  have hlarge : (k : ℝ) ≤ (η / 2) * ((L + 1 : ℕ) : ℝ) := by nlinarith
  apply hcount N (by omega) L hcrit F hdyadic hnon
  intro p hp
  have hcard := hlarge.trans (small_density η hη p.1 p.2 L (hdense p hp))
  exact_mod_cast hcard

end PaperP1.GeneralGraphHostCount
