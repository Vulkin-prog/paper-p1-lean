module

public import PaperP1.Model.PairSquareClassFourier
public import PaperP1.Arithmetic.UnitAffineSigns
public import PaperP1.Arithmetic.CompressionRank
public import PaperP1.Model.RegularStarts

/-! # Exact actual covariance of a private normalized pair, indexed by even units -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateUnitCovariance

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedWindowSets PaperP1.NormalizedUnitCount PaperP1.UnitIntersectionEquiv
  PaperP1.UnitAffineSigns PaperP1.PairSquareClassFourier

local instance privateUnitCovariancePrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance (P : Prop) : Decidable P := Classical.propDecidable P

def signedUnitSum (a b x y L : ℕ) : ℝ :=
  ∑ w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L)),
    if w ≠ 0 then (binarySign (leftParity w + rightParity w) : ℝ) else 0

theorem private_marginals {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hL : 0 < L)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ ∧ infiniteMarginal y L = (2 ^ L : ℝ)⁻¹ := by
  obtain ⟨hrx, hry⟩ := CompressionRank.private_local_ranks ha hb hx hy hprivate
  constructor
  · apply RegularStarts.marginal_on_regular (N := x) (by omega) hL
    exact RegularStarts.mem_regularStarts.mpr ⟨mem_Ico.mpr ⟨le_rfl, by omega⟩, hrx⟩
  · apply RegularStarts.marginal_on_regular (N := y) (by omega) hL
    exact RegularStarts.mem_regularStarts.mpr ⟨mem_Ico.mpr ⟨le_rfl, by omega⟩, hry⟩

theorem common_sum_eq_unit_sum {M a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hL : 0 < L)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L))
    (ωx ωy : SampleSpace M) (hstartX : startSystem M x L ωx = startRhs L)
    (hstartY : startSystem M y L ωy = startRhs L) :
    (∑ z : ↥(squareClassSpace x L ⊓ squareClassSpace y L),
      if z ≠ 0 then realCharacter (parityPairing M z.val) ωx *
        realCharacter (parityPairing M z.val) ωy else 0) = signedUnitSum a b x y L := by
  let e := unitIntersectionEquiv ha hb hx hy hprivate
  unfold signedUnitSum
  symm
  apply Fintype.sum_equiv e.toEquiv
  intro w
  by_cases hw : w = 0
  · subst w
    have he0 : e.toEquiv 0 = 0 := e.map_zero
    exact (ite_eq_right (not_ne_iff.mpr rfl)).trans
      (ite_eq_right (not_ne_iff.mpr he0)).symm
  · have hew : e.toEquiv w ≠ 0 := fun h ↦ hw (e.injective (h.trans e.map_zero.symm))
    have hsign : (binarySign (leftParity w + rightParity w) : ℝ) =
        realCharacter (parityPairing M (e.toEquiv w).val) ωx *
          realCharacter (parityPairing M (e.toEquiv w).val) ωy := by
      change (binarySign (leftParity w + rightParity w) : ℝ) =
      realCharacter (parityPairing M (unitIntersectionEquiv ha hb hx hy hprivate w).val) ωx *
        realCharacter (parityPairing M (unitIntersectionEquiv ha hb hx hy hprivate w).val) ωy
      rw [unitIntersectionEquiv_apply]
      exact (paired_real_character ha hb hx hy hL ωx ωy hstartX hstartY w).symm
    exact (ite_eq_left hw).trans (hsign.trans (ite_eq_left hew).symm)

theorem private_pair_centered_moment {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hL : 0 < L)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    infiniteFamilyCenteredMoment L (centres x y) =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * signedUnitSum a b x y L := by
  obtain ⟨hpx, hpy⟩ := private_marginals ha hb hx hy hL hprivate
  let M := max x y + L
  have hcutX : x + L ≤ M := by dsimp [M]; omega
  have hcutY : y + L ≤ M := by dsimp [M]; omega
  have hp : 0 < (2 ^ L : ℝ)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) _)
  obtain ⟨ωx, hstartX⟩ := (infiniteMarginal_pos_iff_compatible hL hcutX).mp (hpx.symm ▸ hp)
  obtain ⟨ωy, hstartY⟩ := (infiniteMarginal_pos_iff_compatible hL hcutY).mp (hpy.symm ▸ hp)
  rw [pair_common_formula hL hcutX hcutY ωx ωy hstartX hstartY,
    common_sum_eq_unit_sum ha hb hx hy hL hprivate ωx ωy hstartX hstartY, hpx, hpy, pow_two]

theorem private_pair_covariance {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x ≠ y) (hL : 0 < L)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    infiniteJointMoment L {x, y} - ((2 ^ L : ℝ)⁻¹) ^ 2 =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * signedUnitSum a b x y L := by
  have h := private_pair_centered_moment ha hb hx hy hL hprivate
  obtain ⟨hpx, hpy⟩ := private_marginals ha hb hx hy hL hprivate
  rw [pair_moment_covariance hxy, hpx, hpy, ← pow_two] at h
  exact h

theorem private_pair_mass {a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hxy : x ≠ y) (hL : 0 < L)
    (hprivate : FiniteEvenSquareClasses.Private (NormalizedWindowSets.union a b x y L)) :
    infiniteJointMoment L {x, y} =
      ((2 ^ L : ℝ)⁻¹) ^ 2 * (1 + signedUnitSum a b x y L) := by
  have h := private_pair_covariance ha hb hx hy hxy hL hprivate
  linarith

end PaperP1.PrivateUnitCovariance
