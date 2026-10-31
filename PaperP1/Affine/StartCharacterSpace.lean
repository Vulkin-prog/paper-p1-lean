/-
Adapted in part from Vulkin-prog/paper-c-lean, the one-start boundary identities
in PaperC/Affine/RelationBoundaryIff.lean, commit
b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0.
Changes: public one-start helpers, Lean 4.36 declarations and namespaces.
The effective square-class/row-space equivalence below is new here.
-/
module

public import PaperP1.Arithmetic.EvenSquareClasses
public import PaperP1.Model.ParityCharacters
public import PaperP1.Affine.EffectiveRows
public import PaperP1.Model.StartProbability

/-! # Square-class images and the actual effective run characters -/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Model PaperP1.Probability

namespace PaperP1.Affine

local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

/-- One finite-cylinder start row is the incidence sum of its endpoint values. -/
theorem startSystem_apply_eq_sum_incidence
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    startSystem M x L ω i =
      ∑ v : Fin (L + 1),
        startIncidenceColumn i v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  rw [startSystem_apply]
  by_cases hi : i.1 = 0
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]

/--
Line-boundary identity for the actual finite-cylinder rows of one start.
-/
theorem sum_startSystem_eq_sum_completeBoundary
    (M x L : ℕ) (ω : SampleSpace M) (u : Fin L → F₂) :
    (∑ i : Fin L, u i * startSystem M x L ω i) =
      ∑ v : Fin (L + 1),
        startCompleteBoundary L u v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  simp_rw [startSystem_apply_eq_sum_incidence]
  calc
    (∑ i : Fin L,
        u i *
          ∑ v : Fin (L + 1),
            startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) =
        ∑ i : Fin L, ∑ v : Fin (L + 1),
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ v : Fin (L + 1), ∑ i : Fin L,
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) :=
      Finset.sum_comm
    _ = ∑ v : Fin (L + 1),
          (∑ i : Fin L, u i * startIncidenceColumn i v) *
            valueBit ω (startCompleteVertexLabel x L v) := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring1
    _ = ∑ v : Fin (L + 1),
          startCompleteBoundary L u v *
            valueBit ω (startCompleteVertexLabel x L v) := by
          simp only [startCompleteBoundary_apply]

theorem parityPairing_vertexParityMap (M x L : ℕ) (w : Fin (L + 1) → F₂)
    (ω : SampleSpace M) :
    parityPairing M (vertexParityMap x L w) ω =
      ∑ v, w v * valueBit ω (startCompleteVertexLabel x L v) := by
  simp only [vertexParityMap_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, parityPairing_parityVec, valueLinear_apply, smul_eq_mul]

theorem relationMap_start_eq_parityPairing (M x L : ℕ) :
    relationMap (startSystem M x L) =
      (parityPairing M).comp ((vertexParityMap x L).comp (startCompleteBoundary L)) := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro ω
  change dotProduct u (startSystem M x L ω) =
    parityPairing M (vertexParityMap x L (startCompleteBoundary L u)) ω
  rw [dotProduct, sum_startSystem_eq_sum_completeBoundary,
    parityPairing_vertexParityMap]

theorem effectiveRowSpace_eq_map_squareClassSpace (M x L : ℕ) :
    effectiveRowSpace (startSystem M x L) =
      (squareClassSpace x L).map (parityPairing M) := by
  rw [effectiveRowSpace, relationMap_start_eq_parityPairing, LinearMap.range_comp,
    ← squareClassSpace_eq_range_boundary]

theorem startCompleteVertexLabel_le_cutoff {M x L : ℕ} (hcut : x + L ≤ M)
    (v : Fin (L + 1)) : startCompleteVertexLabel x L v ≤ M := by
  unfold startCompleteVertexLabel
  split_ifs <;> omega

theorem squareClassSpace_le_boundedPrimeParity {M x L : ℕ} (hcut : x + L ≤ M) :
    squareClassSpace x L ≤ boundedPrimeParity M := by
  rintro c ⟨w, rfl⟩
  change vertexParityMap x L w.val ∈ boundedPrimeParity M
  rw [vertexParityMap_apply]
  apply Submodule.sum_mem
  intro v _
  exact (boundedPrimeParity M).smul_mem (w.val v)
    (parityVec_mem_boundedPrimeParity (startCompleteVertexLabel_le_cutoff hcut v))

def squareClassToRow (M x L : ℕ) :
    squareClassSpace x L →ₗ[F₂] effectiveRowSpace (startSystem M x L) :=
  ((parityPairing M).domRestrict (squareClassSpace x L)).codRestrict
    (effectiveRowSpace (startSystem M x L)) (fun c => by
      rw [effectiveRowSpace_eq_map_squareClassSpace]
      exact Submodule.mem_map.mpr ⟨c.val, c.property, rfl⟩)

@[simp]
theorem squareClassToRow_apply (M x L : ℕ) (c : squareClassSpace x L) :
    (squareClassToRow M x L c).val = parityPairing M c.val := rfl

theorem squareClassToRow_injective {M x L : ℕ} (hcut : x + L ≤ M) :
    Function.Injective (squareClassToRow M x L) := by
  intro c d h
  apply Subtype.ext
  exact parityPairing_injOn_bounded M
    (squareClassSpace_le_boundedPrimeParity hcut c.property)
    (squareClassSpace_le_boundedPrimeParity hcut d.property)
    (congrArg Subtype.val h)

theorem squareClassToRow_surjective (M x L : ℕ) :
    Function.Surjective (squareClassToRow M x L) := by
  intro f
  have hf := f.property
  simp only [effectiveRowSpace_eq_map_squareClassSpace] at hf
  obtain ⟨c, hc, hcf⟩ := Submodule.mem_map.mp hf
  exact ⟨⟨c, hc⟩, Subtype.ext hcf⟩

/-- Supported effective square classes and actual row characters are linearly
equivalent, including all local relations in the image quotient. -/
def squareClassEquivRow {M x L : ℕ} (hcut : x + L ≤ M) :
    squareClassSpace x L ≃ₗ[F₂] effectiveRowSpace (startSystem M x L) :=
  LinearEquiv.ofBijective (squareClassToRow M x L)
    ⟨squareClassToRow_injective hcut, squareClassToRow_surjective M x L⟩

theorem finrank_squareClassSpace_eq_effectiveRows {M x L : ℕ} (hcut : x + L ≤ M) :
    Module.finrank F₂ (squareClassSpace x L) =
      Module.finrank F₂ (effectiveRowSpace (startSystem M x L)) :=
  (squareClassEquivRow hcut).finrank_eq

theorem card_squareClassSpace (x L : ℕ) :
    Fintype.card (squareClassSpace x L) = 2 ^ Module.finrank F₂ (squareClassSpace x L) :=
  card_eq_two_pow_finrank (V := squareClassSpace x L)

theorem exactMarginal_start_eq_squareClass_rank {M x L : ℕ} (hL : 0 < L)
    (hcut : x + L ≤ M) (hc : Compatible (startSystem M x L) (startRhs L)) :
    exactMarginal (cylinderProbability M) (fun y => startIndicator y L) x =
      (2 ^ Module.finrank F₂ (squareClassSpace x L) : ℝ)⁻¹ := by
  rw [exactMarginal_start_eq_affineMass M x L hL, compatible_mass_eq_effectiveRate _ _ hc]
  have hcard := Fintype.card_congr (squareClassEquivRow hcut).toEquiv
  unfold effectiveRate
  rw [← hcard, card_squareClassSpace]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem squareClassAffineSign_independent_of_solution (M x L : ℕ) {a a' : SampleSpace M}
    (ha : startSystem M x L a = startSystem M x L a') (s : squareClassSpace x L) :
    realCharacter (parityPairing M s.val) a = realCharacter (parityPairing M s.val) a' := by
  exact effectiveRowSign_independent_of_solution (startSystem M x L) ha (squareClassToRow M x L s)

end PaperP1.Affine
