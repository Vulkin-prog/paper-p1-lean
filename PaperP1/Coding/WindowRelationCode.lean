module

public import PaperP1.Coding.LocalRigidityCode
public import PaperP1.Arithmetic.EvenSquareClasses

/-!
# All even square relations in a consecutive window

Large prime coordinates force every relation to be supported on the actual
defective vertices. Restriction to those vertices injects the full relation
code into the concrete small-prime augmented code. This connects the finite
Griesmer obstruction to the manuscript's actual square-relation dimension.
-/

@[expose] public noncomputable section

namespace PaperP1.WindowRelationCode

open PaperP1.Arithmetic Finset LocalRigidityCode LocalDefectBound DefectivePredicate

local instance windowRelationPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def windowParityMap (U B : ℕ) : (Fin B → F₂) →ₗ[F₂] (ℕ →₀ F₂) :=
  Fintype.linearCombination F₂ (fun i ↦ parityVec (U + i.val))

def windowEvennessMap (B : ℕ) : (Fin B → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ (fun _ ↦ 1)

/-- All even selections with square product, represented by full parity vectors. -/
def windowRelationCode (U B : ℕ) : Submodule F₂ (Fin B → F₂) :=
  LinearMap.ker (windowParityMap U B) ⊓ LinearMap.ker (windowEvennessMap B)

theorem mem_windowRelationCode {U B : ℕ} (w : Fin B → F₂) :
    w ∈ windowRelationCode U B ↔
      (∑ i, w i • parityVec (U + i.val) = 0) ∧ (∑ i, w i = 0) := by
  simp only [windowRelationCode, Submodule.mem_inf, LinearMap.mem_ker,
    windowParityMap, windowEvennessMap, Fintype.linearCombination_apply,
    smul_eq_mul, mul_one]

theorem coefficient_zero_of_mem {U B : ℕ} (w : windowRelationCode U B)
    (i : Fin B) (hi : ¬HDefective B (U + i.val)) : (w : Fin B → F₂) i = 0 :=
  PrivateWindowPrimes.coefficient_zero_of_not_defective _
    ((mem_windowRelationCode _).mp w.property).1 i hi

/-- A defect value's actual position in the original window. -/
def defectIndex (U B : ℕ) (hB : 1 ≤ B) (i : Fin (defectValues U B).card) : Fin B :=
  ⟨defectEnum U B i - U, by
    have h := defectEnum_bounds U B i
    omega⟩

theorem defectIndex_value (U B : ℕ) (hB : 1 ≤ B)
    (i : Fin (defectValues U B).card) :
    U + (defectIndex U B hB i).val = defectEnum U B i := by
  have h := (defectEnum_bounds U B i).1
  exact Nat.add_sub_of_le h

theorem defectIndex_injective (U B : ℕ) (hB : 1 ≤ B) :
    Function.Injective (defectIndex U B hB) := by
  intro i j hij
  apply defectEnum_injective U B
  rw [← defectIndex_value U B hB i, ← defectIndex_value U B hB j, hij]

theorem exists_defectIndex {U B : ℕ} (hB : 1 ≤ B) (j : Fin B)
    (hj : HDefective B (U + j.val)) :
    ∃ i : Fin (defectValues U B).card, defectIndex U B hB i = j := by
  have hmem : U + j.val ∈ defectValues U B := by
    apply mem_defectsInInterval.mpr
    have := j.isLt
    exact ⟨by omega, by omega, hj⟩
  let v : defectValues U B := ⟨U + j.val, hmem⟩
  let i := (defectValues U B).equivFin v
  have hi : defectEnum U B i = U + j.val := by
    simp only [defectEnum, i, Equiv.symm_apply_apply, v]
  refine ⟨i, ?_⟩
  apply Fin.ext
  have hval := defectIndex_value U B hB i
  omega

/-- Reindex a sum supported on the actual defect coordinates. -/
theorem sum_defectIndex {M : Type*} [AddCommMonoid M] {U B : ℕ} (hB : 1 ≤ B)
    (g : Fin B → M) (hg : ∀ j, ¬HDefective B (U + j.val) → g j = 0) :
    (∑ i, g (defectIndex U B hB i)) = ∑ j, g j := by
  classical
  calc
    (∑ i, g (defectIndex U B hB i)) =
        ∑ j ∈ Finset.univ.image (defectIndex U B hB), g j :=
      (Finset.sum_image (defectIndex_injective U B hB).injOn).symm
    _ = ∑ j, g j := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      apply hg j
      intro hdef
      obtain ⟨i, hi⟩ := exists_defectIndex hB j hdef
      exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)

/-- Coordinate restriction, before imposing either code condition. -/
def defectRestriction (U B : ℕ) (hB : 1 ≤ B) :
    (Fin B → F₂) →ₗ[F₂] (Fin (defectValues U B).card → F₂) where
  toFun w i := w (defectIndex U B hB i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem defectRestriction_apply (U B : ℕ) (hB : 1 ≤ B) (w : Fin B → F₂)
    (i : Fin (defectValues U B).card) :
    defectRestriction U B hB w i = w (defectIndex U B hB i) := rfl

theorem restriction_mem_defectCode {U B : ℕ} (hB : 1 ≤ B)
    (w : windowRelationCode U B) :
    defectRestriction U B hB w ∈ defectCode U B := by
  have hw := (mem_windowRelationCode _).mp w.property
  have heven : (∑ i, (w : Fin B → F₂) (defectIndex U B hB i)) = 0 :=
    (sum_defectIndex hB (w : Fin B → F₂) (coefficient_zero_of_mem w)).trans hw.2
  have hparity : (∑ i, (w : Fin B → F₂) (defectIndex U B hB i) •
      parityVec (defectEnum U B i)) = 0 := by
    have h := sum_defectIndex hB
      (fun j ↦ (w : Fin B → F₂) j • parityVec (U + j.val))
      (fun j hj ↦ by rw [coefficient_zero_of_mem w j hj, zero_smul])
    simpa only [defectIndex_value] using h.trans hw.1
  apply LinearMap.mem_ker.mpr
  funext j
  refine Fin.lastCases ?_ (fun k ↦ ?_) j
  · simpa only [DefectCodeRank.augmentedParityMap,
      DefectCodeRank.augmentedColumnMap_apply_last, defectRestriction_apply,
      Pi.zero_apply] using heven
  · have hp := congrArg (fun v : ℕ →₀ F₂ ↦ v (smallPrime B k)) hparity
    simpa only [DefectCodeRank.augmentedParityMap,
      DefectCodeRank.augmentedColumnMap_apply_castSucc,
      DefectCodeRank.smallParityColumn, defectRestriction_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply, Pi.zero_apply] using hp

/-- The restriction map on the full, actual even square-relation code. -/
def relationRestriction (U B : ℕ) (hB : 1 ≤ B) :
    windowRelationCode U B →ₗ[F₂] defectCode U B :=
  ((defectRestriction U B hB).comp (windowRelationCode U B).subtype).codRestrict
    (defectCode U B) (restriction_mem_defectCode hB)

theorem relationRestriction_injective (U B : ℕ) (hB : 1 ≤ B) :
    Function.Injective (relationRestriction U B hB) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  by_cases hj : HDefective B (U + j.val)
  · obtain ⟨i, hi⟩ := exists_defectIndex hB j hj
    have h := congrFun (congrArg Subtype.val hxy) i
    change (x : Fin B → F₂) (defectIndex U B hB i) =
      (y : Fin B → F₂) (defectIndex U B hB i) at h
    simpa only [hi] using h
  · rw [coefficient_zero_of_mem x j hj, coefficient_zero_of_mem y j hj]

theorem window_relation_finrank_le_defectCode (U B : ℕ) (hB : 1 ≤ B) :
    Module.finrank F₂ (windowRelationCode U B) ≤ Module.finrank F₂ (defectCode U B) :=
  LinearMap.finrank_le_finrank_of_injective (relationRestriction_injective U B hB)

/-- The finite Griesmer inequality in Lemma 2.1, for the dimension of the
full even square-relation code of the actual window. -/
theorem window_relation_griesmer {U B t : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (ht : t ≤ Module.finrank F₂ (windowRelationCode U B)) :
    (∑ i ∈ Finset.range t, ⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊) - t ≤
      primeCount B + 1 :=
  defectCode_griesmer hB hU
    (ht.trans (window_relation_finrank_le_defectCode U B hB))

/-- The full parity encoding agrees with literal rational square products;
the appended condition is precisely even cardinality of the selection. -/
theorem mem_windowRelationCode_iff_even_square {U B : ℕ} (hU : 0 < U)
    (w : Fin B → F₂) :
    w ∈ windowRelationCode U B ↔
      Even (HammingBound.wordSupport w).card ∧
        IsSquare (∏ i ∈ HammingBound.wordSupport w, ((U + i.val : ℕ) : ℚ)) := by
  classical
  have hsum : (∑ i, w i) = ((HammingBound.wordSupport w).card : F₂) := by
    simpa only [mul_one, Finset.sum_const, nsmul_eq_mul, mul_one] using
      (DefectCodeRank.sum_wordSupport_eq_weighted_sum w (fun _ ↦ 1)).symm
  have hparity : (∑ i, w i • parityVec (U + i.val)) =
      ∑ i ∈ HammingBound.wordSupport w, parityVec (U + i.val) := by
    rw [HammingBound.wordSupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rcases binary_eq_zero_or_one (w i) with hz | ho
    · simp only [hz, ne_eq, not_true_eq_false, ite_false, zero_smul]
    · simp [ho]
  rw [mem_windowRelationCode, hsum, hparity]
  rw [sum_parityVec_zero_iff_rational_square _ _ (fun i _ ↦ by omega),
    ZMod.natCast_eq_zero_iff, ← even_iff_two_dvd]
  exact and_comm

/-- A finite prime-count comparison rules out the specified dimension. -/
theorem window_relation_finrank_lt {U B t : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (hobstruction : primeCount B + 1 < GriesmerBound.griesmerSum t (rungeDistance U B) - t) :
    Module.finrank F₂ (windowRelationCode U B) < t := by
  by_contra h
  have hg := window_relation_griesmer hB hU (Nat.le_of_not_gt h)
  rw [← GriesmerBound.griesmerSum_eq_sum_ceil _ _ (rungeDistance_pos hB hU)] at hg
  omega

/-- The same inequality over the reals; the subtraction here is ordinary
subtraction, rather than truncated natural subtraction. -/
theorem window_relation_griesmer_real {U B t : ℕ} (hB : 1 ≤ B) (hU : 2 * B ≤ U)
    (ht : t ≤ Module.finrank F₂ (windowRelationCode U B)) :
    (∑ i ∈ Finset.range t, (⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊ : ℝ)) - t ≤
      (primeCount B : ℝ) + 1 := by
  have h := window_relation_griesmer hB hU ht
  have hs : t ≤ ∑ i ∈ Finset.range t,
      ⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊ := by
    rw [← GriesmerBound.griesmerSum_eq_sum_ceil _ _ (rungeDistance_pos hB hU)]
    exact GriesmerBound.length_le_griesmerSum _ _
  have hr : (((∑ i ∈ Finset.range t,
      ⌈(rungeDistance U B : ℝ) / (2 : ℝ) ^ i⌉₊) - t : ℕ) : ℝ) ≤ primeCount B + 1 := by
    exact_mod_cast h
  simpa only [Nat.cast_sub hs, Nat.cast_sum] using hr

end PaperP1.WindowRelationCode
