module

public import PaperP1.Model.PrimitiveConnectedGeometry
public import PaperP1.Model.SecondOrderIndependentDeficit
public import PaperP1.Asymptotics.Primitive256Tail

/-! # Exactly the 254 fixed-order hypotheses in article 15.13, with constants chosen before N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteConnectedActivity254

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

def families (N L r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (connectedFamilies (dyadicBlock N) L r).filter fun I ↦ runCompatibleNullity L I ≤ 2 * L

def Hypothesis (C β : ℝ) : Prop :=
  ∀ r : ℕ, 3 ≤ r → r ≤ 256 → ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (∑ I ∈ families N L r, |infiniteCenteredCoefficient L I|) ≤ A * (N : ℝ) ^ (-β + ε)

theorem uniform_weighted (u C β ε : ℝ) (hu : 0 ≤ u) (hε : 0 < ε) (hfixed : Hypothesis C β) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 3 ≤ I.card ∧ I.card ≤ 256 ∧ Connected L I ∧ runCompatibleNullity L I ≤ 2 * L) →
      (∑ I ∈ F, u ^ I.card * |infiniteCenteredCoefficient L I|) ≤ (N : ℝ) ^ (-β + ε) := by
  classical
  have hper (i : Fin 254) := hfixed (i.val + 3) (by omega) (by omega) (ε / 2) (by positivity)
  choose A _hA Nt ht using hper
  let B : ℝ := ∑ i : Fin 254, u ^ (i.val + 3) * A i
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption B (-β + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NF + univ.sup Nt, by omega, ?_⟩
  intro N hN L hband F hF
  let P := (N : ℝ) ^ (-β + ε / 2)
  let Fi := fun i : Fin 254 ↦ F.filter fun I ↦ I.card = i.val + 3
  let w := fun I : Finset ℕ ↦ u ^ I.card * |infiniteCenteredCoefficient L I|
  have hw (I : Finset ℕ) : 0 ≤ w I := mul_nonneg (pow_nonneg hu _) (abs_nonneg _)
  have hcover : F ⊆ univ.biUnion Fi := by
    intro I hI
    have hd := hF I hI
    let i : Fin 254 := ⟨I.card - 3, by omega⟩
    refine mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hI, ?_⟩⟩
    dsimp only [i]
    omega
  have hbound (i : Fin 254) : (∑ I ∈ Fi i, w I) ≤ (u ^ (i.val + 3) * A i) * P := by
    have hsub : Fi i ⊆ families N L (i.val + 3) := by
      intro I hI
      obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
      have hd := hF I hIF
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hd.1, hcard⟩, hd.2.2.2.1⟩, hd.2.2.2.2⟩
    have hNi : Nt i ≤ univ.sup Nt := le_sup (f := Nt) (mem_univ i)
    have hsum := (sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ abs_nonneg (infiniteCenteredCoefficient L I))).trans
      (ht i N (by omega) L hband)
    calc
      _ = u ^ (i.val + 3) * ∑ I ∈ Fi i, |infiniteCenteredCoefficient L I| := by
        rw [mul_sum]
        apply sum_congr rfl
        intro I hI
        dsimp only [w]
        rw [(mem_filter.mp hI).2]
      _ ≤ u ^ (i.val + 3) * (A i * P) := mul_le_mul_of_nonneg_left hsum (pow_nonneg hu _)
      _ = _ := by ring
  calc
    _ ≤ ∑ I ∈ univ.biUnion Fi, w I := sum_le_sum_of_subset_of_nonneg hcover (fun I _ _ ↦ hw I)
    _ ≤ ∑ i : Fin 254, ∑ I ∈ Fi i, w I := GraphStarWeights.sum_biUnion_le_nonneg univ Fi w hw
    _ ≤ ∑ i : Fin 254, (u ^ (i.val + 3) * A i) * P := sum_le_sum fun i _ ↦ hbound i
    _ = B * P := (sum_mul ..).symm
    _ ≤ (N : ℝ) ^ ((-β + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

theorem uniform_primitives (u C β ε : ℝ) (hu : 0 < u) (hβ : β ≤ 4 / 3) (hε : 0 < ε)
    (hfixed : Hypothesis C β) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑ D ∈ SecondOrderIndependentDeficit.primitives G L, ActualComponentRemainder.weight L u D) ≤
        (N : ℝ) ^ (-β + ε) := by
  classical
  obtain ⟨NS, _hNS, hs⟩ := uniform_weighted u C β (ε / 2) hu.le (by positivity) hfixed
  obtain ⟨NT, _hNT, ht⟩ := Primitive256Tail.uniform_centered u C (ε / 2) hu (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 (-β + ε / 2) (ε / 2) (by positivity)
  refine ⟨10 + NS + NT + NF, by omega, ?_⟩
  intro N hN L hband G hG
  let F := SecondOrderIndependentDeficit.primitives G L
  let Small := F.filter fun I ↦ I.card ≤ 256
  let Large := F.filter fun I ↦ ¬I.card ≤ 256
  have hsmall : (∑ I ∈ Small, ActualComponentRemainder.weight L u I) ≤ (N : ℝ) ^ (-β + ε / 2) := by
    apply hs N (by omega) L hband Small
    intro I hI
    obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
    obtain ⟨hIG, hthree, hprim⟩ := mem_filter.mp hIF
    have hsub := (mem_powerset.mp hIG).trans hG
    refine ⟨hsub, hthree, hcard, PrimitiveConnectedGeometry.connected L I hprim, ?_⟩
    exact (PrimitiveConnectedGeometry.compatible_nullity_le (by omega : 0 < N) I hsub hprim).trans (by omega)
  have hlarge : (∑ I ∈ Large, ActualComponentRemainder.weight L u I) ≤ (N : ℝ) ^ (-β + ε / 2) := by
    apply (ht N (by omega) L hband Large ?_).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith only [hβ]))
    intro I hI
    obtain ⟨hIF, hcard⟩ := mem_filter.mp hI
    obtain ⟨hIG, _hthree, hprim⟩ := mem_filter.mp hIF
    exact ⟨(mem_powerset.mp hIG).trans hG, by omega, hprim⟩
  have hsplit := sum_filter_add_sum_filter_not F (fun I ↦ I.card ≤ 256) (ActualComponentRemainder.weight L u)
  have hsum : (∑ I ∈ F, ActualComponentRemainder.weight L u I) ≤ 2 * (N : ℝ) ^ (-β + ε / 2) := by
    linarith only [hsmall, hlarge, hsplit]
  calc
    _ ≤ 2 * (N : ℝ) ^ (-β + ε / 2) := hsum
    _ ≤ (N : ℝ) ^ ((-β + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.FiniteConnectedActivity254
