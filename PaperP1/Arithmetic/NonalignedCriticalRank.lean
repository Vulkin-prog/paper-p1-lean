module

public import PaperP1.Analysis.ShortBasisCurveScale
public import PaperP1.Arithmetic.LinearCurveAlignment
public import PaperP1.Asymptotics.HeightControlledCommonCurveCount
public import PaperP1.Arithmetic.DegreeWeightedCurveGridBudget

/-! # The full critical-band nonaligned rank theorem without BCN

The actual common-curve coefficient height and maximum partial-degree fibre
factor supply the full short-support range internally. No external point-count
property occurs in the theorem arguments.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedCriticalRank

open Finset Polynomial PaperP1.Arithmetic PaperP1.FreeComponentRank PaperP1.ShortBasisActualSpace
  PaperP1.ShortBasisCurveScale PaperP1.ShortBasisTheorem PaperP1.CriticalBandScale
  PaperP1.CriticalWindowGeometry PaperP1.BivariateTotalDegree PaperP1.CurveIntegerFibres

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : CommRing ℤ[X][X] := inferInstance
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

theorem critical_rank_bound (ε : ℝ) (hε : 0 < ε) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ PaperP1.Model.dyadicBlock N, ∀ y ∈ PaperP1.Model.dyadicBlock N,
      ¬ CompressedTargetAlignment.Aligned 1 x y L →
        (pairIntersectionRank x y L : ℝ) ≤
          ((2 / 3) * Real.log 2 + ε) * ((L + 1 : ℕ) : ℝ) := by
  classical
  let a := extractionExponent ε
  obtain ⟨ha, haHalf, hchoice⟩ := extractionExponent_choice ε hε
  change 0 < a at ha
  change a < 1 / 2 at haHalf
  change (2 / 3) * Real.log (1 / a) = (2 / 3) * Real.log 2 + ε / 4 at hchoice
  let b : ℝ := (a + 1 / 2) / 2
  have hab : a < b := by dsimp [b]; linarith
  have hb : 0 < b := by dsimp [b]; linarith
  have hbHalf : b < 1 / 2 := by dsimp [b]; linarith
  obtain ⟨KD, KS, _hKD, hKS, hshort⟩ := article_13_1 a ha (by linarith)
  obtain ⟨Bs, _hBs, hs⟩ := support_budget_eventually a b KS hab hb (by linarith) hKS
  obtain ⟨Bp, _hBp, hp⟩ := point_threshold_eventually b upperScale hbHalf upperScale_pos
  obtain ⟨Bd, _hBd, hd⟩ := dimension_budget_eventually b (ε / 4) hbHalf (by positivity)
  obtain ⟨Be, _hBe, he⟩ := extraction_error_eventually KD (ε / 4) (by positivity)
  obtain ⟨Bt, _hBt, ht⟩ := rank_threshold_eventually (ε / 2) (by positivity)
  obtain ⟨Bg, _hBg, hg⟩ := HeightControlledCommonCurveCount.power_cap
    b hbHalf (ε / 8) (by positivity)
  let B₀ := max Bs (max Bp (max Bd (max Be (max Bt Bg))))
  obtain ⟨Ngeom, hgeom⟩ := uniform_geometry C B₀
  obtain ⟨Nshort, hNshort⟩ := hshort C
  refine ⟨max Ngeom Nshort, ?_⟩
  intro N hN L hband x hx y hy hnon
  let B := L + 1
  obtain ⟨hNtwo, hBmin, hBtwo, hBN, _hBlo, hBhi⟩ := hgeom N (by omega) L hband
  change B₀ ≤ B at hBmin
  change 2 ≤ B at hBtwo
  change 8 * B ≤ N at hBN
  change (B : ℝ) ≤ upperScale * Real.log N at hBhi
  have hBs : Bs ≤ B := by dsimp [B₀] at hBmin; omega
  have hBp : Bp ≤ B := by dsimp [B₀] at hBmin; omega
  have hBd : Bd ≤ B := by dsimp [B₀] at hBmin; omega
  have hBe : Be ≤ B := by dsimp [B₀] at hBmin; omega
  have hBt : Bt ≤ B := by dsimp [B₀] at hBmin; omega
  have hBg : Bg ≤ B := by dsimp [B₀] at hBmin; omega
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hxN := (mem_Ico.mp hx).1
  have hyN := (mem_Ico.mp hy).1
  have hx₂ := (mem_Ico.mp hx).2
  have hy₂ := (mem_Ico.mp hy).2
  obtain ⟨cert, hdim, hsupport, _hnonzero⟩ := hNshort N (by omega) L hband x hx y hy
  change (pairIntersectionRank x y L : ℝ) - (2 / 3) * (B : ℝ) * Real.log (1 / a) -
    KD * ((B : ℝ) / Real.sqrt (Real.log B)) ≤ (Module.finrank F₂ cert.space : ℝ) at hdim
  have hlead : (2 / 3) * (B : ℝ) * Real.log (1 / a) =
      ((2 / 3) * Real.log 2 + ε / 4) * B := by
    calc
      _ = ((2 / 3) * Real.log (1 / a)) * B := by ring
      _ = _ := by rw [hchoice]
  rw [hlead] at hdim
  have herror := mul_le_mul_of_nonneg_right (he B hBe) hBpos.le
  have herror' : KD * ((B : ℝ) / Real.sqrt (Real.log B)) ≤ (ε / 4) * B := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using herror
  by_contra hnot
  have hrank : ((2 / 3) * Real.log 2 + ε) * (B : ℝ) < (pairIntersectionRank x y L : ℝ) :=
    lt_of_not_ge hnot
  have hlargeSpace : (ε / 2) * (B : ℝ) < (Module.finrank F₂ cert.space : ℝ) := by
    nlinarith only [hrank, hdim, herror']
  have htReal : (9 : ℝ) ≤ (Module.finrank F₂ cert.space : ℝ) := (ht B hBt).trans hlargeSpace.le
  have htNat : 9 ≤ Module.finrank F₂ cert.space := by exact_mod_cast htReal
  let q := halfBudget b B
  obtain ⟨hqone, hqB, hsbudget⟩ := hs B hBs
  change 1 ≤ q at hqone
  change q ≤ B at hqB
  have hqReal : (q : ℝ) ≤ (B : ℝ) ^ b := Nat.floor_le (Real.rpow_nonneg hBpos.le b)
  have hsNat (i : cert.index) :
      (physicalCoefficients x y L (cert.basis i).val).support.card ≤ 2 * q := by
    have hi := hsupport i
    change ((physicalCoefficients x y L (cert.basis i).val).support.card : ℝ) ≤
      KS * ((B : ℝ) ^ a * Real.log B / Real.log (Real.log B)) at hi
    have hi' : ((physicalCoefficients x y L (cert.basis i).val).support.card : ℝ) ≤
        KS * (B : ℝ) ^ a * Real.log B / Real.log (Real.log B) := by
      simpa only [div_eq_mul_inv, mul_assoc] using hi
    exact_mod_cast hi'.trans hsbudget
  have hpointThreshold := hp B hBp q hqReal (N : ℝ) (by exact_mod_cast (show 1 < N by omega)) hBhi
  obtain ⟨curve, hpoint, hD, hHeight⟩ := CurveFromCompleteRelations.common_curve
    x y L q (by omega) (by omega) cert (by omega) hqone hqB hsNat (N : ℝ)
    (by exact_mod_cast hxN) (by exact_mod_cast hyN)
    (by exact_mod_cast hx₂.le) (by exact_mod_cast hy₂.le) hpointThreshold
  have hDreal : (totalDegree curve.polynomial : ℝ) ≤ 48 * (B : ℝ) ^ b := by
    have hDcast : (totalDegree curve.polynomial : ℝ) ≤ 48 * (q : ℝ) := by exact_mod_cast hD
    linarith
  have hDne := LinearCurveAlignment.nonaligned_degree_ne_one x y L (by dsimp [B] at hBtwo; omega)
    cert curve htNat (by dsimp [B] at hBN; omega) (by dsimp [B] at hBN; omega) hpoint hnon
  have hDpos : 0 < totalDegree curve.polynomial :=
    curve.degreeY_pos.trans_le (BivariateCurveDegrees.degreeY_le_total curve.polynomial)
  have hDtwo : 2 ≤ totalDegree curve.polynomial := by omega
  have hgrid := DegreeWeightedCurveGridBudget.rank_budget x y L cert curve
  have hloss := (degree_loss_of_power_bound (B : ℝ) b (totalDegree curve.polynomial) hBpos hDreal).trans
    (hd B hBd)
  have hcount := hg B hBg q hqone hqReal curve.polynomial curve.irreducible hDtwo hD hHeight
  change ((integerGrid curve.polynomial (L + 1)).card : ℝ) /
    ((max (BivariateDegrees.degreeX curve.polynomial) (BivariateDegrees.degreeY curve.polynomial) : ℕ) : ℝ) ≤
      (ε / 8) * B at hcount
  nlinarith only [hlargeSpace, hgrid, hloss, hcount, mul_pos hε hBpos]

end PaperP1.NonalignedCriticalRank
