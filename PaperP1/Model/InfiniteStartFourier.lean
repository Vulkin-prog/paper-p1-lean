module

public import PaperP1.Model.InfiniteStarts

/-!
# Full-support Fourier formulas under the infinite prime-sign measure

Admissibility is positivity of the actual infinite-model marginal. It supplies
the local affine witnesses through the proved finite-cylinder equivalence.
The formula and both nullity bounds retain all heterogeneous marginals.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Affine PaperP1.Algebra PaperP1.Probability PaperP1.Model

namespace PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem infiniteMarginal_pos_iff_compatible {M x L : ℕ} (hL : 0 < L) (hcut : x + L ≤ M) :
    0 < infiniteMarginal x L ↔ Compatible (startSystem M x L) (startRhs L) := by
  rw [infiniteMarginal_eq_finite hcut, exactMarginal_start_pos_iff M x L hL]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem infiniteAdmissibleCompatibility (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    ∀ i, Compatible (startSystem M (g i) L) (startRhs L) :=
  fun i => (infiniteMarginal_pos_iff_compatible hL (hcut i)).mp (hp i)

def infiniteAdmissibleWitness (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    ι → SampleSpace M :=
  startFamilyWitness M L g (infiniteAdmissibleCompatibility M L g hL hcut hp)

theorem infinite_start_full_support_formula (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      ∑ s : (i : ι) → startFamilySpace M L g i,
        if IsFullSupportRelation (startFamilySpace M L g) s then
          affineTupleSign (startFamilySpace M L g)
            (infiniteAdmissibleWitness M L g hL hcut hp) s else 0 := by
  rw [infiniteFamilyCenteredMoment_eq_finite M L g hcut]
  simp_rw [infiniteMarginal_eq_finite (hcut _)]
  exact start_full_support_formula M L g hL
    (infiniteAdmissibleCompatibility M L g hL hcut hp)

theorem infinite_start_centered_moment_bound [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      ((2 ^ relativeNullity (startFamilySpace M L g) : ℝ) - 1) := by
  rw [infiniteFamilyCenteredMoment_eq_finite M L g hcut]
  simp_rw [infiniteMarginal_eq_finite (hcut _)]
  exact start_centered_moment_bound M L g hL
    (infiniteAdmissibleCompatibility M L g hL hcut hp)

theorem infinite_start_centered_moment_coarse_bound [Nonempty ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L) :
    |infiniteFamilyCenteredMoment L g| ≤ (∏ i, infiniteMarginal (g i) L) *
      (2 ^ relativeNullity (startFamilySpace M L g) : ℝ) := by
  refine (infinite_start_centered_moment_bound M L g hL hcut hp).trans ?_
  exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one)
    (Finset.prod_nonneg fun i _ => le_of_lt (hp i))

theorem infinite_start_full_support_relation_of_ne_zero
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L)
    (hcut : ∀ i, g i + L ≤ M) (hp : ∀ i, 0 < infiniteMarginal (g i) L)
    (hn : infiniteFamilyCenteredMoment L g ≠ 0) :
    ∃ s : (i : ι) → startFamilySpace M L g i,
      IsFullSupportRelation (startFamilySpace M L g) s := by
  rw [infiniteFamilyCenteredMoment_eq_finite M L g hcut] at hn
  exact start_full_support_relation_of_ne_zero M L g hL
    (infiniteAdmissibleCompatibility M L g hL hcut hp) hn

end PaperP1.Model.InfiniteStarts
