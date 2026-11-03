module

public import PaperP1.Model.ActualComponentRemainder
public import PaperP1.Model.CenteredSourcePairBound
public import PaperP1.Model.OrdinaryIndependentDeficit
public import PaperP1.Model.IndependentExtensionDeficit
public import PaperP1.Combinatorics.SeedComplementSum
public import PaperP1.Combinatorics.RestrictedSeedComplements

/-! # Positive actual joint mass outside a retained class: independent, failed source-pair, and nonlinear component terms -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonretainedPositiveMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.ActualComponentRemainder

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def residual (G : Finset ℕ) (L K : ℕ) (η : ℝ) (E : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  G.powerset.filter fun I ↦ I.Nonempty ∧ I.card ≤ K ∧ (runRelativeNullity L I : ℝ) ≤ η * L ∧ I ∉ E

theorem mem_residual (G I : Finset ℕ) (L K : ℕ) (η : ℝ) (E : Finset (Finset ℕ)) :
    I ∈ residual G L K η E ↔ I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧
      (runRelativeNullity L I : ℝ) ≤ η * L ∧ I ∉ E := by
  simp only [residual, mem_filter, mem_powerset]

theorem weighted_term (L : ℕ) (I D : Finset ℕ) (hDI : D ⊆ I) (u c : ℝ) :
    u ^ I.card * (c * ∏ x ∈ I \ D, infiniteMarginal x L) =
      (u ^ D.card * c) * ∏ x ∈ I \ D, u * infiniteMarginal x L := by
  have hcard := card_sdiff_add_card_eq_card hDI
  rw [← hcard, pow_add, prod_mul_distrib, prod_const]
  ring

theorem expansion_bound (L : ℕ) (I : Finset ℕ) :
    infiniteJointMoment L I ≤ (∏ x ∈ I, infiniteMarginal x L) +
      ∑ D ∈ I.powerset.erase ∅, |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L := by
  have h := CompressedJointMoments.infinite_uncentered_expansion L I
  have hsum := sum_erase_add I.powerset
    (fun D ↦ |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L) (empty_mem_powerset I)
  simp only [CompressedJointMoments.centered_empty, abs_one, sdiff_empty, one_mul] at hsum
  calc
    _ = ∑ D ∈ I.powerset, infiniteCenteredCoefficient L D * ∏ x ∈ I \ D, infiniteMarginal x L := h
    _ ≤ ∑ D ∈ I.powerset, |infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L :=
      sum_le_sum fun D _ ↦ mul_le_mul_of_nonneg_right (le_abs_self _)
        (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    _ = _ := by linarith only [hsum]

theorem pointwise_bound (G : Finset ℕ) (L K : ℕ) (hL : 0 < L) (η u : ℝ) (hu : 0 ≤ u)
    (E : Finset (Finset ℕ)) (hE : E ⊆ G.powersetCard 2) (hq : ∀ e ∈ E, 0 < infiniteJointMoment L e)
    (I : Finset ℕ) (hIG : I ⊆ G) (hsize : I.card ≤ K) (hcap : (runRelativeNullity L I : ℝ) ≤ η * L) :
    u ^ I.card * infiniteJointMoment L I ≤ (∏ x ∈ I, u * infiniteMarginal x L) +
      (∑ e ∈ E, if e ⊆ I then u ^ 2 * infiniteJointMoment L e * ∏ x ∈ I \ e, u * infiniteMarginal x L else 0) +
      ∑ D ∈ residual G L K η E, if D ⊆ I then weight L u D * ∏ x ∈ I \ D, u * infiniteMarginal x L else 0 := by
  classical
  let A := I.powerset.erase ∅
  let b := fun D : Finset ℕ ↦ u ^ I.card * (|infiniteCenteredCoefficient L D| * ∏ x ∈ I \ D, infiniteMarginal x L)
  let w := fun x ↦ u * infiniteMarginal x L
  have hw (x : ℕ) : 0 ≤ w x := mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hdata (D : Finset ℕ) (hD : D ∈ A) : D ⊆ I ∧ D.Nonempty := by
    obtain ⟨hne, hD⟩ := mem_erase.mp hD
    exact ⟨mem_powerset.mp hD, nonempty_iff_ne_empty.mpr hne⟩
  have hgood : (∑ D ∈ A.filter (fun D ↦ D ∈ E), b D) ≤
      ∑ e ∈ E, if e ⊆ I then u ^ 2 * infiniteJointMoment L e * ∏ x ∈ I \ e, w x else 0 := by
    have hsub : A.filter (fun D ↦ D ∈ E) ⊆ E := fun _ h ↦ (mem_filter.mp h).2
    calc
      _ ≤ ∑ D ∈ A.filter (fun D ↦ D ∈ E),
          if D ⊆ I then u ^ 2 * infiniteJointMoment L D * ∏ x ∈ I \ D, w x else 0 := by
        apply sum_le_sum
        intro D hD
        obtain ⟨hDA, hDE⟩ := mem_filter.mp hD
        have hDI := (hdata D hDA).1
        have hcard := (mem_powersetCard.mp (hE hDE)).2
        have hc := (CenteredSourcePairBound.pointwise L hL D hcard (hq D hDE)).2
        rw [ite_eq_left hDI]
        dsimp only [b, w]
        rw [weighted_term L I D hDI u _, hcard]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg hu _))
          (prod_nonneg fun x _ ↦ hw x)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ ↦ by
        split_ifs
        · exact mul_nonneg (mul_nonneg (pow_nonneg hu _) (infiniteJointMoment_nonneg L D))
            (prod_nonneg fun x _ ↦ hw x)
        · exact le_rfl)
  have hrest : (∑ D ∈ A.filter (fun D ↦ D ∉ E), b D) ≤
      ∑ D ∈ residual G L K η E, if D ⊆ I then weight L u D * ∏ x ∈ I \ D, w x else 0 := by
    have hsub : A.filter (fun D ↦ D ∉ E) ⊆ residual G L K η E := by
      intro D hD
      obtain ⟨hDA, hDE⟩ := mem_filter.mp hD
      obtain ⟨hDI, hne⟩ := hdata D hDA
      have hmono := relativeNullityOn_mono (fun x ↦ squareClassSpace x L) hDI
      change runRelativeNullity L D ≤ runRelativeNullity L I at hmono
      exact (mem_residual G D L K η E).mpr ⟨hDI.trans hIG, hne,
        (card_le_card hDI).trans hsize, (by exact_mod_cast hmono : (runRelativeNullity L D : ℝ) ≤ runRelativeNullity L I).trans hcap, hDE⟩
    calc
      _ = ∑ D ∈ A.filter (fun D ↦ D ∉ E), if D ⊆ I then weight L u D * ∏ x ∈ I \ D, w x else 0 := by
        apply sum_congr rfl
        intro D hD
        have hDI := (hdata D (mem_filter.mp hD).1).1
        rw [ite_eq_left hDI]
        exact weighted_term L I D hDI u _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (fun D _ _ ↦ by
        split_ifs
        · exact mul_nonneg (mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) (prod_nonneg fun x _ ↦ hw x)
        · exact le_rfl)
  have hsplit := sum_filter_add_sum_filter_not A (fun D ↦ D ∈ E) b
  have hbound := mul_le_mul_of_nonneg_left (expansion_bound L I) (pow_nonneg hu I.card)
  rw [mul_add, mul_sum] at hbound
  have hindep : u ^ I.card * (∏ x ∈ I, infiniteMarginal x L) = ∏ x ∈ I, w x := by
    dsimp only [w]
    rw [prod_mul_distrib, prod_const]
  rw [hindep] at hbound
  change u ^ I.card * infiniteJointMoment L I ≤ (∏ x ∈ I, w x) + ∑ D ∈ A, b D at hbound
  change u ^ I.card * infiniteJointMoment L I ≤ (∏ x ∈ I, w x) + _ + _
  linarith only [hgood, hrest, hsplit, hbound]

theorem pair_deficit_bound (G : Finset ℕ) (L : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (E F : Finset (Finset ℕ))
    (hF : ∀ I ∈ F, I ⊆ G ∧ ¬RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I) :
    (∑ I ∈ F, ∑ e ∈ E, if e ⊆ I then u ^ 2 * infiniteJointMoment L e *
      ∏ x ∈ I \ e, u * infiniteMarginal x L else 0) ≤
      u ^ 2 * ∑ e ∈ E, infiniteJointMoment L e * IndependentExtensionDeficit.deficit G e
        (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L u := by
  classical
  let S := fun x ↦ squareClassSpace x L
  let w := fun x ↦ u * infiniteMarginal x L
  have hw (x : ℕ) : 0 ≤ w x := mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  rw [sum_comm, mul_sum]
  apply sum_le_sum
  intro e _he
  let W := SubspaceFamilyRank.span S e
  let : Fintype W := MinimalRelativeRelations.spanFintype S e
  let FE := F.filter fun I ↦ e ⊆ I
  have hfiber : (∑ I ∈ FE, ∏ x ∈ I \ e, w x) ≤
      ∑ A ∈ IndependentExtensionDeficit.families (G \ e) W L, ∏ x ∈ A, w x := by
    apply RestrictedSeedComplements.fiber_bound FE e _ w hw
    intro I hI
    obtain ⟨hIF, heI⟩ := mem_filter.mp hI
    obtain ⟨hIG, hnot⟩ := hF I hIF
    refine ⟨heI, (IndependentExtensionDeficit.mem_families _ _ _ _).mpr ⟨?_, ?_⟩⟩
    · exact sdiff_subset_sdiff_left e hIG
    · intro hdirect
      have hz := (IndependentExtensionDeficit.direct_iff_nullity W L (I \ e)).mp hdirect
      have hdis : Disjoint e (I \ e) := disjoint_left.mpr fun x hx he ↦ (mem_sdiff.mp he).2 hx
      have hcomp := (MinimalRelativeRelations.zero_iff_compressed S e (I \ e) hdis).mp hz
      rw [union_sdiff_of_subset heI] at hcomp
      exact hnot (Or.inr ⟨e, _he, hcomp⟩)
  calc
    _ = (u ^ 2 * infiniteJointMoment L e) * ∑ I ∈ FE, ∏ x ∈ I \ e, w x := by
      simp only [FE, w, sum_filter, mul_sum, mul_ite, mul_zero]
    _ ≤ (u ^ 2 * infiniteJointMoment L e) *
        ∑ A ∈ IndependentExtensionDeficit.families (G \ e) W L, ∏ x ∈ A, w x :=
      mul_le_mul_of_nonneg_left hfiber (mul_nonneg (pow_nonneg hu _) (infiniteJointMoment_nonneg L e))
    _ = _ := by
      rw [IndependentExtensionDeficit.deficit_eq_product_weights]
      ring

theorem finite_bound (G : Finset ℕ) (L K : ℕ) (hL : 0 < L) (η u : ℝ) (hu : 0 ≤ u)
    (E F : Finset (Finset ℕ)) (hE : E ⊆ G.powersetCard 2) (hq : ∀ e ∈ E, 0 < infiniteJointMoment L e)
    (hF : ∀ I ∈ F, I ⊆ G ∧ I.Nonempty ∧ I.card ≤ K ∧ (runRelativeNullity L I : ℝ) ≤ η * L ∧
      ¬RetainedDependence.Retained (fun x ↦ squareClassSpace x L) E I) :
    (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤
      OrdinaryIndependentDeficit.mass G L (fun x ↦ u * infiniteMarginal x L) +
      u ^ 2 * (∑ e ∈ E, infiniteJointMoment L e * IndependentExtensionDeficit.deficit G e
        (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L u) +
      Real.exp (∑ x ∈ G, u * infiniteMarginal x L) *
        (Real.exp ((∑ e ∈ G.powersetCard 2, weight L u e) +
          ∑ C ∈ higher G L K η, weight L u C) - 1 - ∑ e ∈ E, weight L u e) := by
  classical
  let T := residual G L K η E
  let w := fun x ↦ u * infiniteMarginal x L
  have hw (x : ℕ) : 0 ≤ w x := mul_nonneg hu (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
  have hground (I : Finset ℕ) (hI : I ∈ F) : I ⊆ G := (hF I hI).1
  have hOrd : (∑ I ∈ F, ∏ x ∈ I, w x) ≤ OrdinaryIndependentDeficit.mass G L w := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro I hI
      have hd := hF I hI
      refine mem_filter.mpr ⟨mem_powerset.mpr hd.1, ?_⟩
      intro hz
      exact hd.2.2.2.2 (Or.inl hz)
    · intro I _ _
      exact prod_nonneg fun x _ ↦ hw x
  have hPair := pair_deficit_bound G L u hu E F (fun I hI ↦ ⟨(hF I hI).1, (hF I hI).2.2.2.2⟩)
  have hRem := SeedComplementSum.finite_bound G F T w (weight L u) hw
    (fun D _ ↦ mul_nonneg (pow_nonneg hu _) (abs_nonneg _)) hground
    (fun D hD ↦ ((mem_residual G D L K η E).mp hD).1)
  have hT := ActualComponentRemainder.finite_bound G L K hL η u hu E T hE
    (fun D hD ↦ (mem_residual G D L K η E).mp hD)
  have hRem2 := hRem.trans (mul_le_mul_of_nonneg_left hT (Real.exp_nonneg _))
  have hpoint := sum_le_sum (fun I hI ↦ pointwise_bound G L K hL η u hu E hE hq I
    (hF I hI).1 (hF I hI).2.2.1 (hF I hI).2.2.2.1)
  simp only [sum_add_distrib] at hpoint
  change (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤ _
  linarith only [hOrd, hPair, hRem2, hpoint]

end PaperP1.NonretainedPositiveMass
