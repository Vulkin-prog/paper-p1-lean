module

public import PaperP1.Asymptotics.TwoBlockComponentHostData

/-! # The actual degree-(a,1) unpinned component graph consequence under two geometric inputs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DegreeOneGraphHostCount

open Finset PaperP1.LargePrimeGraph PaperP1.PinnedGraphResolution PaperP1.LargePrimeGraphResolution
  PaperP1.TwoBlockComponentSquares PaperP1.TwoBlockComponentPatterns PaperP1.SplitRadicalPatternPool
  PaperP1.SplitRadicalPointHeight

def components (x y L a : ℕ) : Finset (largePrimeGraph x y L).ConnectedComponent := by
  classical
  exact (unpinnedComponents (largePrimeGraph x y L) (pinnedVertices x y L)).filter
    fun c ↦ (vertices x y L c).toLeft.card = a ∧ (vertices x y L c).toRight.card = 1

theorem mem_components (x y L a : ℕ) (c : (largePrimeGraph x y L).ConnectedComponent) :
    c ∈ components x y L a ↔
      ¬ ComponentPinned (largePrimeGraph x y L) (pinnedVertices x y L) c ∧
      (vertices x y L c).toLeft.card = a ∧ (vertices x y L c).toRight.card = 1 := by
  classical
  simp only [components, mem_filter, mem_unpinnedComponents]

theorem exists_system_of_components (k a x y L : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hcount : k ≤ (components x y L a).card) :
    ∃ q ∈ pool k L (10 * (L + 1)) (a + 1), SmoothDegreeOneHostCount.Valid a (a + 1) q ∧
      ∃ w : Fin k → ℤ, ∀ i,
        w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) (x : ℤ) * ((y : ℤ) + q.1.2 i) := by
  classical
  let U := components x y L a
  let e : U ≃ Fin U.card := Fintype.equivFinOfCardEq (Fintype.card_coe U)
  let f : Fin k → U := fun i ↦ e.symm (Fin.castLE hcount i)
  have hf : Function.Injective f := e.symm.injective.comp (Fin.castLE_injective hcount)
  let c : Fin k → (largePrimeGraph x y L).ConnectedComponent := fun i ↦ (f i).val
  have hc : Function.Injective c := fun _ _ h ↦ hf (Subtype.ext h)
  have hdata (i) := (mem_components x y L a (c i)).mp (f i).property
  have hleft (i) : (leftOffsets x y L (c i)).card = a := (left_card x y L (c i)).trans (hdata i).2.1
  have hright (i) : (rightOffsets x y L (c i)).card = 1 := (right_card x y L (c i)).trans (hdata i).2.2
  exact TwoBlockComponentHostData.exists_pattern k a (a + 1) x y L hx hy c hc
    (fun i ↦ (hdata i).1) hleft hright le_rfl

theorem uniform_hosts (C ε : ℝ) (a : ℕ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k (a + 1) →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, k ≤ (components p.1 p.2 L a).card) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := SmoothDegreeOneHostCount.uniform_hosts C ε 10 (a + 1) hε
  refine ⟨k, ?_⟩
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
  have hnon' : ∀ p ∈ U, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 p.1.natAbs p.2.natAbs L := by
    intro p hp ha1
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact hnon q hq ha1
  have hsystems : ∀ p ∈ U, ∃ q ∈ pool k L (10 * (L + 1)) (a + 1),
      SmoothDegreeOneHostCount.Valid a (a + 1) q ∧ ∃ w : Fin k → ℤ,
        ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * (p.2 + q.1.2 i) := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    have hx : 2 ≤ q.1 := by have h := (mem_Ico.mp (hdyadic q hq).1).1; omega
    have hy : 2 ≤ q.2 := by have h := (mem_Ico.mp (hdyadic q hq).2).1; omega
    exact exists_system_of_components k a q.1 q.2 L hx hy (hcomponents q hq)
  have hbound := hcount N (by omega) L (10 * (L + 1)) hcrit le_rfl a ha U hdyadic' hnon' hsystems
  simpa only [hcard] using hbound

theorem alignment_symm {D x y L : ℕ} (h : CompressedTargetAlignment.Aligned D x y L) :
    CompressedTargetAlignment.Aligned D y x L := by
  obtain ⟨r, t, hr, ht, hcop, hrB, htB, he⟩ := h
  refine ⟨t, r, ht, hr, hcop.symm, htB, hrB, ?_⟩
  simpa only [abs_sub_comm, Nat.add_comm] using he

theorem uniform_either_orientation (C ε : ℝ) (a : ℕ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k (a + 1) →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, k ≤ (components p.1 p.2 L a).card ∨ k ≤ (components p.2 p.1 L a).card) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := uniform_hosts C ε a ha hε
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk hCover hPila
  refine ⟨2 * A, by positivity, N₀, ?_⟩
  intro N hN L hcrit F hdyadic hnon hcomponents
  classical
  let U := F.filter fun p ↦ k ≤ (components p.1 p.2 L a).card
  let V := F \ U
  let R := V.image Prod.swap
  have hU : (U.card : ℝ) ≤ A * (N : ℝ) ^ ε :=
    hcount N hN L hcrit U (fun p hp ↦ hdyadic p (mem_filter.mp hp).1)
      (fun p hp ↦ hnon p (mem_filter.mp hp).1) (fun _ hp ↦ (mem_filter.mp hp).2)
  have hRdyadic : ∀ p ∈ R, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact (hdyadic q (mem_sdiff.mp hq).1).symm
  have hRnon : ∀ p ∈ R, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L := by
    intro p hp ha1 halign
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact hnon q (mem_sdiff.mp hq).1 ha1 (alignment_symm halign)
  have hRcomponents : ∀ p ∈ R, k ≤ (components p.1 p.2 L a).card := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    obtain ⟨hqF, hqU⟩ := mem_sdiff.mp hq
    rcases hcomponents q hqF with hleft | hright
    · exact False.elim (hqU (mem_filter.mpr ⟨hqF, hleft⟩))
    · exact hright
  have hR := hcount N hN L hcrit R hRdyadic hRnon hRcomponents
  have hRcard : R.card = V.card := card_image_of_injective _ Prod.swap_injective
  have hpartition : V.card + U.card = F.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  rw [hRcard] at hR
  have hpartitionR : (V.card : ℝ) + U.card = F.card := by exact_mod_cast hpartition
  nlinarith

theorem uniform_mixed_orientations (C ε : ℝ) (a : ℕ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k (a + 1) →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ F : Finset (ℕ × ℕ),
        (∀ p ∈ F, p.1 ∈ Model.dyadicBlock N ∧ p.2 ∈ Model.dyadicBlock N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned 1 p.1 p.2 L) →
        (∀ p ∈ F, 2 * k ≤ (components p.1 p.2 L a).card + (components p.2 p.1 L a).card) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := uniform_either_orientation C ε a ha hε
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk hCover hPila
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L hcrit F hdyadic hnon hcomponents
  apply hcount N hN L hcrit F hdyadic hnon
  intro p hp
  have h := hcomponents p hp
  omega

end PaperP1.DegreeOneGraphHostCount
