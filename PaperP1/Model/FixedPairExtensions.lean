module

public import PaperP1.Model.RelativeWindowFamilies
public import PaperP1.Model.AbsoluteActivityDecomposition
public import PaperP1.Model.IndependentTargetDeficit
public import PaperP1.Probability.SeedProductBound
public import PaperP1.Combinatorics.GraphStarWeights

/-! # Actual failed extensions of a pair are covered by minimal relative seeds with exact heterogeneous weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedPairExtensions

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FamilyIndependentMass

local instance fixedPairExtensionsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def sourceSpace (e : Finset ℕ) (L : ℕ) := SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e

def extensions (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (k : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((G \ e).powersetCard k).filter fun U ↦
    ¬ RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ U)

def layer (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (k h : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (extensions G L e k).filter fun U ↦
    ∃ A ∈ RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L), A ⊆ U

def deficit (G : Finset ℕ) (L k : ℕ) : ℝ :=
  ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| * independentMass (extensions G L e k) L

theorem mem_extensions (G : Finset ℕ) (L : ℕ) (e U : Finset ℕ) (k : ℕ) :
    U ∈ extensions G L e k ↔ U ⊆ G \ e ∧ U.card = k ∧
      ¬ CompressedBlocks.Direct (fun x ↦ squareClassSpace x L) e (e ∪ U) := by
  classical
  simp only [extensions, mem_filter, mem_powersetCard,
    CompressedBlocks.direct_iff_compressed _ e (e ∪ U) subset_union_left]
  exact and_assoc

theorem exists_seed (G : Finset ℕ) (L : ℕ) (e U : Finset ℕ) (k : ℕ) (hU : U ∈ extensions G L e k) :
    ∃ h ∈ Icc 1 k, ∃ A ∈ RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L), A ⊆ U := by
  classical
  let : Fintype (sourceSpace e L) := MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) e
  obtain ⟨hUG, hnot⟩ := mem_filter.mp hU
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hUG
  have hdisj : Disjoint e U := disjoint_left.mpr (fun x hxe hxU ↦ (mem_sdiff.mp (hsub hxU)).2 hxe)
  have hpos : 0 < MinimalRelativeRelations.nullity (sourceSpace e L) (fun x ↦ squareClassSpace x L) U := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hnot ((MinimalRelativeRelations.zero_iff_compressed (fun x ↦ squareClassSpace x L) e U hdisj).mp hz)
  obtain ⟨A, hAU, hne, hApos, hproper⟩ := MinimalRelativeRelations.exists_minimal
    (sourceSpace e L) (fun x ↦ squareClassSpace x L) U hpos
  refine ⟨A.card, mem_Icc.mpr ⟨hne.card_pos, (card_le_card hAU).trans_eq hcard⟩, A, ?_, hAU⟩
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hAU.trans hsub, rfl⟩,
    RelativeWindowFamilies.minimal_witnesses L (sourceSpace e L) A hApos hproper⟩

theorem extension_cover (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (k : ℕ) :
    independentMass (extensions G L e k) L ≤ ∑ h ∈ Icc 1 k, independentMass (layer G L e k h) L := by
  classical
  have hsub : extensions G L e k ⊆ (Icc 1 k).biUnion (layer G L e k) := by
    intro U hU
    obtain ⟨h, hh, A, hA, hAU⟩ := exists_seed G L e U k hU
    exact mem_biUnion.mpr ⟨h, hh, mem_filter.mpr ⟨hU, A, hA, hAU⟩⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun U _ _ ↦ prod_nonneg
    (fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))).trans
    (GraphStarWeights.sum_biUnion_le_nonneg (Icc 1 k) (layer G L e k)
      (fun U ↦ ∏ x ∈ U, infiniteMarginal x L)
      (fun U ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))

theorem layer_bound (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (k h : ℕ) (hh : h ≤ k) :
    independentMass (layer G L e k h) L ≤
      independentMass (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L *
        ((∑ x ∈ G \ e, infiniteMarginal x L) ^ (k - h) / ((k - h).factorial : ℝ)) := by
  classical
  apply SeedProductBound.power_bound (G \ e) (fun x ↦ infiniteMarginal x L)
    (fun x ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) h (k - h)
  · intro A hA
    exact mem_powersetCard.mp (mem_filter.mp hA).1
  · intro U hU
    obtain ⟨hbase, hseed⟩ := mem_filter.mp hU
    obtain ⟨hsub, hcard, _hnot⟩ := (mem_extensions G L e U k).mp hbase
    exact ⟨hsub, by omega, hseed⟩

theorem remaining_factor_bound (μ M : ℝ) (hμ : 0 ≤ μ) (hM : 0 ≤ M) (hcap : μ ≤ M) (k h : ℕ) :
    μ ^ (k - h) / ((k - h).factorial : ℝ) ≤ (M + 1) ^ k := by
  have hfact : (1 : ℝ) ≤ (k - h).factorial := by exact_mod_cast Nat.factorial_pos (k - h)
  calc
    _ ≤ μ ^ (k - h) := div_le_self (pow_nonneg hμ _) hfact
    _ ≤ M ^ (k - h) := pow_le_pow_left₀ hμ hcap _
    _ ≤ (M + 1) ^ (k - h) := pow_le_pow_left₀ hM (by linarith) _
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (Nat.sub_le k h)

theorem mass_bound (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) (k : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hmean : (∑ x ∈ G \ e, infiniteMarginal x L) ≤ M) :
    independentMass (extensions G L e k) L ≤ (M + 1) ^ k *
      ∑ h ∈ Icc 1 k, independentMass (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L := by
  apply (extension_cover G L e k).trans
  rw [mul_sum]
  apply sum_le_sum
  intro h hh
  have hfactor := remaining_factor_bound _ M
    (sum_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L) hM hmean k h
  have hseed : 0 ≤ independentMass (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L :=
    sum_nonneg fun A _ ↦ prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L
  exact (layer_bound G L e k h (mem_Icc.mp hh).2).trans
    ((mul_le_mul_of_nonneg_left hfactor hseed).trans_eq (mul_comm _ _))

theorem unary_cost_eq (G : Finset ℕ) (L : ℕ) (hL : 0 < L) :
    (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| *
      independentMass (RelativeWindowFamilies.families (G \ e) L 1 (sourceSpace e L)) L) =
      IndependentTargetDeficit.deficit G L := by
  classical
  unfold IndependentTargetDeficit.deficit
  rw [sum_filter]
  apply sum_congr rfl
  intro e he
  rw [RelativeWindowFamilies.unary_mass]
  by_cases hdep : IndependentTargetDeficit.dependentPair L e
  · rw [ite_eq_left hdep]
    have hfilter : (G \ e).filter (fun z ↦ squareClassSpace z L ⊓ sourceSpace e L ≠ ⊥) =
        (G \ e).filter (IndependentTargetDeficit.targetDependent L e) :=
      filter_congr fun _ _ ↦ Iff.rfl
    rw [hfilter]
  · have hzero : runRelativeNullity L e = 0 := Nat.eq_zero_of_not_pos hdep
    have hne : e.Nonempty := card_pos.mp (by have h := (mem_powersetCard.mp he).2; omega)
    rw [ite_eq_right hdep, AbsoluteActivityDecomposition.centered_zero_direct L hL e hne hzero, abs_zero, zero_mul]

theorem finite_bound (G : Finset ℕ) (L k : ℕ) (hL : 0 < L) (hk : 1 ≤ k)
    (M Q : ℝ) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hmean : ∀ e ∈ G.powersetCard 2, (∑ x ∈ G \ e, infiniteMarginal x L) ≤ M)
    (hseed : ∀ e ∈ G.powersetCard 2, ∀ h ∈ Icc 2 k,
      independentMass (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L ≤ Q) :
    deficit G L k ≤ (M + 1) ^ k * (IndependentTargetDeficit.deficit G L +
      (k : ℝ) * Q * ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) := by
  classical
  let f := fun e h ↦ independentMass
    (RelativeWindowFamilies.families (G \ e) L h (sourceSpace e L)) L
  have hsum (e : Finset ℕ) (he : e ∈ G.powersetCard 2) :
      ∑ h ∈ Icc 1 k, f e h ≤ f e 1 + (k : ℝ) * Q := by
    have herase : (Icc 1 k).erase 1 = Icc 2 k := by
      ext h
      simp only [mem_erase, mem_Icc]
      omega
    have hsplit := sum_erase_add (Icc 1 k) (f e) (mem_Icc.mpr ⟨le_rfl, hk⟩)
    rw [herase] at hsplit
    have hcard : ((Icc 2 k).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (show (Icc 2 k).card ≤ k by rw [Nat.card_Icc]; omega)
    calc
      _ = f e 1 + ∑ h ∈ Icc 2 k, f e h := by linarith only [hsplit]
      _ ≤ f e 1 + ∑ _h ∈ Icc 2 k, Q :=
        add_le_add le_rfl (sum_le_sum fun h hh ↦ hseed e he h hh)
      _ = f e 1 + ((Icc 2 k).card : ℝ) * Q := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard hQ)
  calc
    _ ≤ ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| *
        ((M + 1) ^ k * (f e 1 + (k : ℝ) * Q)) := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left ((mass_bound G L e k M hM (hmean e he)).trans
        (mul_le_mul_of_nonneg_left (hsum e he) (pow_nonneg (by linarith) _))) (abs_nonneg _)
    _ = (M + 1) ^ k * ∑ e ∈ G.powersetCard 2,
        (|infiniteCenteredCoefficient L e| * f e 1 + (k : ℝ) * Q * |infiniteCenteredCoefficient L e|) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e _
      ring
    _ = (M + 1) ^ k * ((∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| * f e 1) +
        (k : ℝ) * Q * ∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e|) := by
      rw [sum_add_distrib, mul_sum]
    _ = _ := by rw [show (∑ e ∈ G.powersetCard 2, |infiniteCenteredCoefficient L e| * f e 1) =
      IndependentTargetDeficit.deficit G L from unary_cost_eq G L hL]

end PaperP1.FixedPairExtensions
