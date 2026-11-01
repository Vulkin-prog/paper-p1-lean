module

public import PaperP1.Arithmetic.UnitIntersectionEquiv
public import PaperP1.Affine.StartVertexSign

/-! # The actual affine signs on even unit coefficients are literal predecessor parities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitAffineSigns

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.UnitIntersectionEquiv PaperP1.StartVertexSign

local instance unitAffineSignPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

def leftParity {a b x y L : ℕ} (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) : F₂ :=
  ∑ u : ↥(units a b x y L), w.val u * if u.val.1 = 0 then 1 else 0

def rightParity {a b x y L : ℕ} (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) : F₂ :=
  ∑ u : ↥(units a b x y L), w.val u * if u.val.2 = 0 then 1 else 0

theorem unitClassMap_evaluation {M a b x y L : ℕ} (ω : SampleSpace M)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) :
    parityPairing M (unitClassMap a b x y L w) ω =
      ∑ u : ↥(units a b x y L), w.val u * valueBit ω (b * startCompleteVertexLabel x L u.val.1) := by
  change parityPairing M (EvenImage.combination (unitData a b x y L) w.val) ω = _
  rw [EvenImage.combination_apply]
  simp only [unitData, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    parityPairing_parityVec, valueLinear_apply, smul_eq_mul]

theorem left_evaluation {M a b x y L : ℕ} (hb : 0 < b) (hx : 2 ≤ x) (hL : 0 < L)
    (ω : SampleSpace M) (hstart : startSystem M x L ω = startRhs L)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) :
    parityPairing M (unitClassMap a b x y L w) ω = leftParity w := by
  have hw : ∑ u : ↥(units a b x y L), w.val u = 0 := by
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property
  have hterm (u : ↥(units a b x y L)) :
      valueBit ω (b * startCompleteVertexLabel x L u.val.1) =
        (valueBit ω b + valueBit ω x) + if u.val.1 = 0 then 1 else 0 := by
    rw [valueBit_mul ω hb.ne' (values_positive hx _ (mem_values.mpr ⟨u.val.1, rfl⟩)).ne',
      vertex_bit ω hL hstart]
    ring
  rw [unitClassMap_evaluation]
  simp_rw [hterm]
  exact zero_sum_shift w.val (fun u ↦ if u.val.1 = 0 then 1 else 0) (valueBit ω b + valueBit ω x) hw

theorem right_evaluation {M a b x y L : ℕ} (ha : 0 < a) (hy : 2 ≤ y) (hL : 0 < L)
    (ω : SampleSpace M) (hstart : startSystem M y L ω = startRhs L)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) :
    parityPairing M (unitClassMap a b x y L w) ω = rightParity w := by
  have hw : ∑ u : ↥(units a b x y L), w.val u = 0 := by
    simpa only [LinearMap.mem_ker, EvenSupportRank.sumMap_apply] using w.property
  have hterm (u : ↥(units a b x y L)) :
      valueBit ω (b * startCompleteVertexLabel x L u.val.1) =
        (valueBit ω a + valueBit ω y) + if u.val.2 = 0 then 1 else 0 := by
    rw [mem_units.mp u.property,
      valueBit_mul ω ha.ne' (values_positive hy _ (mem_values.mpr ⟨u.val.2, rfl⟩)).ne',
      vertex_bit ω hL hstart]
    ring
  rw [unitClassMap_evaluation]
  simp_rw [hterm]
  exact zero_sum_shift w.val (fun u ↦ if u.val.2 = 0 then 1 else 0) (valueBit ω a + valueBit ω y) hw

theorem paired_real_character {M a b x y L : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hL : 0 < L) (ωx ωy : SampleSpace M)
    (hstartX : startSystem M x L ωx = startRhs L) (hstartY : startSystem M y L ωy = startRhs L)
    (w : LinearMap.ker (EvenSupportRank.sumMap F₂ ↥(units a b x y L))) :
    realCharacter (parityPairing M (unitClassMap a b x y L w)) ωx *
      realCharacter (parityPairing M (unitClassMap a b x y L w)) ωy =
        (binarySign (leftParity w + rightParity w) : ℝ) := by
  rw [realCharacter, realCharacter, left_evaluation hb hx hL ωx hstartX,
    right_evaluation ha hy hL ωy hstartY, binarySign_add, Int.cast_mul]

end PaperP1.UnitAffineSigns
