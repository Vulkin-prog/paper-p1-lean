module

public import PaperP1.Model.SquareClassRelations
public import PaperP1.Model.InfiniteStartFourier

/-!
# Full-support Fourier formula in the manuscript square-class spaces

The indices are the images of even vertex selections in prime-exponent
parity space. The rational-square criterion and boundary equivalence identify
these spaces with the manuscript's positive square-class images. All actual
marginals and centered moments are taken under the infinite prime-sign law.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
open PaperP1.Model.InfiniteRademacher

namespace PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product of the local affine signs, each evaluated at a local solution. -/
def squareClassTupleSign (M L : ℕ) (g : ι → ℕ) (a : ι → SampleSpace M)
    (s : (i : ι) → squareClassFamilySpace L g i) : ℝ :=
  ∏ i, realCharacter (parityPairing M (s i).val) (a i)

omit [DecidableEq ι] in
theorem affineTupleSign_squareClassFamilyEquiv (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (a : ι → SampleSpace M)
    (s : (i : ι) → squareClassFamilySpace L g i) :
    affineTupleSign (startFamilySpace M L g) a (squareClassFamilyEquivRow M L g hcut s) =
      squareClassTupleSign M L g a s := by
  simp only [affineTupleSign, squareClassFamilyEquivRow_apply, squareClassTupleSign]

theorem reindex_full_support_sum (M L : ℕ) (g : ι → ℕ)
    (hcut : ∀ i, g i + L ≤ M) (a : ι → SampleSpace M) :
    (∑ r : (i : ι) → startFamilySpace M L g i,
      if IsFullSupportRelation (startFamilySpace M L g) r then
        affineTupleSign (startFamilySpace M L g) a r else 0) =
    ∑ s : (i : ι) → squareClassFamilySpace L g i,
      if IsFullSupportRelation (squareClassFamilySpace L g) s then
        squareClassTupleSign M L g a s else 0 := by
  symm
  apply Fintype.sum_equiv (squareClassFamilyEquivRow M L g hcut).toEquiv
  intro s
  change (if IsFullSupportRelation (squareClassFamilySpace L g) s then
      squareClassTupleSign M L g a s else 0) =
    if IsFullSupportRelation (startFamilySpace M L g)
        (squareClassFamilyEquivRow M L g hcut s) then
      affineTupleSign (startFamilySpace M L g) a (squareClassFamilyEquivRow M L g hcut s) else 0
  rw [squareClassFamily_full_relation_iff, affineTupleSign_squareClassFamilyEquiv]

/-- Article Lemma 4.2: the full-support formula with effective square classes,
actual heterogeneous marginals and the actual infinite-model centered moment. -/
theorem squareClass_full_support_formula (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      ∑ s : (i : ι) → squareClassFamilySpace L g i,
        if IsFullSupportRelation (squareClassFamilySpace L g) s then
          squareClassTupleSign M L g (infiniteAdmissibleWitness M L g hL hcut hp) s else 0 := by
  rw [infinite_start_full_support_formula M L g hL hcut hp,
    reindex_full_support_sum M L g hcut]

theorem squareClass_centered_moment_bound [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      ((2 ^ relativeNullity (squareClassFamilySpace L g) : ℝ) - 1) := by
  rw [relativeNullity_squareClassFamily_eq_rows M L g hcut]
  exact infinite_start_centered_moment_bound M L g hL hcut hp

theorem squareClass_centered_moment_coarse_bound [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      (2 ^ relativeNullity (squareClassFamilySpace L g) : ℝ) := by
  rw [relativeNullity_squareClassFamily_eq_rows M L g hcut]
  exact infinite_start_centered_moment_coarse_bound M L g hL hcut hp

theorem squareClass_full_relation_of_ne_zero
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L)
    (hn : infiniteFamilyCenteredMoment L g ≠ 0) :
    ∃ s : (i : ι) → squareClassFamilySpace L g i,
      IsFullSupportRelation (squareClassFamilySpace L g) s := by
  obtain ⟨r, hr⟩ := infinite_start_full_support_relation_of_ne_zero M L g hL hcut hp hn
  let s := (squareClassFamilyEquivRow M L g hcut).symm r
  refine ⟨s, (squareClassFamily_full_relation_iff M L g hcut s).mp ?_⟩
  simpa only [s, LinearEquiv.apply_symm_apply] using hr

/-- The source's finite-set coefficient is the same actual Bochner moment
when its factors are indexed by the corresponding finite subtype. -/
theorem infiniteCenteredCoefficient_subtype (L : ℕ) (I : Finset ℕ) :
    (∫ ω, ∏ x ∈ I, ((indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)
      ∂infiniteRademacherMeasure) =
      infiniteFamilyCenteredMoment L (fun x : I => x.val) := by
  unfold infiniteFamilyCenteredMoment
  congr 1
  funext ω
  symm
  rw [Finset.univ_eq_attach]
  exact Finset.prod_attach I (fun x =>
    (indicatorValue (infiniteStartIndicator x L ω) : ℝ) - infiniteMarginal x L)

/-- The full aligned conclusion of article Lemma 4.2, with an explicitly
consistent affine sign prescription and the two asserted bounds. -/
def SquareClassFourierConclusion (M L : ℕ) (g : ι → ℕ) : Prop :=
  ∃ a : ι → SampleSpace M,
    (∀ i, startSystem M (g i) L (a i) = startRhs L) ∧
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      (∑ s : (i : ι) → squareClassFamilySpace L g i,
        if IsFullSupportRelation (squareClassFamilySpace L g) s then
          squareClassTupleSign M L g a s else 0) ∧
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      ((2 ^ relativeNullity (squareClassFamilySpace L g) : ℝ) - 1) ∧
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      (2 ^ relativeNullity (squareClassFamilySpace L g) : ℝ) ∧
    (infiniteFamilyCenteredMoment L g ≠ 0 →
      ∃ s : (i : ι) → squareClassFamilySpace L g i,
        IsFullSupportRelation (squareClassFamilySpace L g) s)

theorem full_support_squareClass_fourier [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    SquareClassFourierConclusion M L g := by
  refine ⟨infiniteAdmissibleWitness M L g hL hcut hp, ?_,
    squareClass_full_support_formula M L g hL hcut hp,
    squareClass_centered_moment_bound M L g hL hcut hp,
    squareClass_centered_moment_coarse_bound M L g hL hcut hp,
    squareClass_full_relation_of_ne_zero M L g hL hcut hp⟩
  intro i
  exact affineWitness_solves _ _ (infiniteAdmissibleCompatibility M L g hL hcut hp i)

/-- Article Lemma 4.2 on any nonempty admissible subfamily of the dyadic block.
The actual finite-set Bochner coefficient is identified by
`infiniteCenteredCoefficient_subtype`; the relative nullity is the dimension
deficit by `relativeNullity_eq_dimension_deficit`. -/
theorem dyadic_squareClass_fourier (N L : ℕ) (I : Finset ℕ) (hL : 0 < L)
    (hI : I.Nonempty) (hsub : I ⊆ dyadicBlock N)
    (hp : ∀ x ∈ I, 0 < infiniteMarginal x L) :
    SquareClassFourierConclusion (dyadicCutoff N L) L (fun x : I => x.val) := by
  classical
  obtain ⟨x, hx⟩ := hI
  let : Nonempty I := ⟨⟨x, hx⟩⟩
  apply full_support_squareClass_fourier _ _ _ hL
  · intro i
    have hi : N ≤ i.val ∧ i.val < 2 * N := Finset.mem_Ico.mp (hsub i.property)
    unfold dyadicCutoff
    omega
  · intro i
    exact hp i.val i.property

end PaperP1.Model.InfiniteStarts
