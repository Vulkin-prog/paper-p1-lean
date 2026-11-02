module

public import PaperP1.Combinatorics.DisjointSubsetIncidence
public import PaperP1.Algebra.ElementarySymmetricBound

/-! # Actual unordered seed covers preserve heterogeneous product weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeedProductBound

open Finset PaperP1.SubsetPowerSums

theorem elementary_bound {ι : Type*} [DecidableEq ι] (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (s k : ℕ) (F T : Finset (Finset ι))
    (hF : ∀ D ∈ F, D ⊆ G ∧ D.card = s)
    (hT : ∀ I ∈ T, I ⊆ G ∧ I.card = s + k ∧ ∃ D ∈ F, D ⊆ I) :
    (∑ I ∈ T, ∏ x ∈ I, p x) ≤
      ∑ D ∈ F, (∏ x ∈ D, p x) * elementary p (G \ D) k := by
  classical
  let f := fun D E : Finset ι ↦ if D ∈ F then (∏ x ∈ D, p x) * ∏ x ∈ E, p x else 0
  have hf (D E : Finset ι) : 0 ≤ f D E := by
    dsimp [f]
    split_ifs
    · exact mul_nonneg (prod_nonneg fun x _ ↦ hp x) (prod_nonneg fun x _ ↦ hp x)
    · exact le_rfl
  have hpoint (I : Finset ι) (hI : I ∈ T) : (∏ x ∈ I, p x) ≤
      ∑ D ∈ I.powersetCard s, f D (I \ D) := by
    obtain ⟨D, hD, hDI⟩ := (hT I hI).2.2
    have hDmem : D ∈ I.powersetCard s := mem_powersetCard.mpr ⟨hDI, (hF D hD).2⟩
    have h := single_le_sum (fun A _ ↦ hf A (I \ A)) hDmem
    have heq : f D (I \ D) = ∏ x ∈ I, p x := by
      dsimp [f]
      rw [ite_eq_left hD, mul_comm, prod_sdiff hDI]
    rwa [heq] at h
  have hsub : T ⊆ G.powersetCard (s + k) := fun I hI ↦ mem_powersetCard.mpr ⟨(hT I hI).1, (hT I hI).2.1⟩
  have hFsub : F ⊆ G.powersetCard s := fun D hD ↦ mem_powersetCard.mpr (hF D hD)
  have hfilter : (G.powersetCard s).filter (fun D ↦ D ∈ F) = F := by
    ext D
    simp only [mem_filter]
    exact ⟨And.right, fun h ↦ ⟨hFsub h, h⟩⟩
  calc
    _ ≤ ∑ I ∈ T, ∑ D ∈ I.powersetCard s, f D (I \ D) := sum_le_sum hpoint
    _ ≤ ∑ I ∈ G.powersetCard (s + k), ∑ D ∈ I.powersetCard s, f D (I \ D) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ ↦ sum_nonneg fun D _ ↦ hf D (I \ D))
    _ = ∑ D ∈ G.powersetCard s, ∑ E ∈ (G \ D).powersetCard k, f D E :=
      DisjointSubsetIncidence.split_sum G s k f
    _ = ∑ D ∈ G.powersetCard s,
        if D ∈ F then (∏ x ∈ D, p x) * elementary p (G \ D) k else 0 := by
      apply sum_congr rfl
      intro D _
      by_cases hD : D ∈ F
      · simp only [f, hD, ite_true, elementary, mul_sum]
      · simp only [f, hD, ite_false, sum_const_zero]
    _ = _ := by rw [← sum_filter, hfilter]

theorem power_bound {ι : Type*} [DecidableEq ι] (G : Finset ι) (p : ι → ℝ)
    (hp : ∀ x, 0 ≤ p x) (s k : ℕ) (F T : Finset (Finset ι))
    (hF : ∀ D ∈ F, D ⊆ G ∧ D.card = s)
    (hT : ∀ I ∈ T, I ⊆ G ∧ I.card = s + k ∧ ∃ D ∈ F, D ⊆ I) :
    (∑ I ∈ T, ∏ x ∈ I, p x) ≤
      (∑ D ∈ F, ∏ x ∈ D, p x) * ((∑ x ∈ G, p x) ^ k / (k.factorial : ℝ)) := by
  calc
    _ ≤ ∑ D ∈ F, (∏ x ∈ D, p x) * elementary p (G \ D) k := elementary_bound G p hp s k F T hF hT
    _ ≤ ∑ D ∈ F, (∏ x ∈ D, p x) * ((∑ x ∈ G, p x) ^ k / (k.factorial : ℝ)) := by
      apply sum_le_sum
      intro D _
      apply mul_le_mul_of_nonneg_left _ (prod_nonneg fun x _ ↦ hp x)
      exact (ElementarySymmetricBound.elementary_le_power_div p hp (G \ D) k).trans
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (sum_nonneg fun x _ ↦ hp x)
          (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun x _ _ ↦ hp x)) k) (Nat.cast_nonneg _))
    _ = _ := (sum_mul _ _ _).symm

end PaperP1.SeedProductBound
