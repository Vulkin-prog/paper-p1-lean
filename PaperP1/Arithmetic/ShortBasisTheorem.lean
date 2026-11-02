module

public import PaperP1.Arithmetic.ShortBasisActualSpace
public import PaperP1.Arithmetic.SmallPrimeShortBasisBudget
public import PaperP1.Arithmetic.RetainedComponentAsymptotics

/-! # The actual short basis, with the source logarithmic dimension and support bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShortBasisTheorem

open Finset Filter PaperP1.Arithmetic PaperP1.LocalDefectBound PaperP1.MediumPrimeColumns
  PaperP1.ShortBasisComponentStage PaperP1.ShortBasisParameters PaperP1.ShortBasisActualSpace
  PaperP1.RetainedComponentAsymptotics PaperP1.CriticalBandScale PaperP1.FreeComponentRank

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance (x y L : ℕ) : DecidableEq (PaperP1.LargePrimeGraph.largePrimeGraph x y L).ConnectedComponent :=
  Classical.decEq _
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : AddCommGroup U :=
  Submodule.addCommGroup U
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (U : Submodule F₂ T) : Module F₂ U := U.module

def blockSize (L : ℕ) : ℝ := ((L + 1 : ℕ) : ℝ)
def smallCutoff (a : ℝ) (L : ℕ) : ℕ := ⌊blockSize L ^ a⌋₊
def componentCutoff (L : ℕ) : ℕ := ⌊Real.log (blockSize L)⌋₊
def dimensionConstant (a K : ℝ) : ℝ := K + 48 + SmallPrimeShortBasisBudget.constant a
def supportConstant (a : ℝ) : ℝ := 11 * SmallPrimeShortBasisBudget.constant a

theorem supportConstant_eq (a : ℝ) : supportConstant a = 352 / a := by
  unfold supportConstant SmallPrimeShortBasisBudget.constant
  ring

theorem constants_pos (a K : ℝ) (ha : 0 < a) (hK : 0 ≤ K) :
    0 < dimensionConstant a K ∧ 0 < supportConstant a := by
  have hc := SmallPrimeShortBasisBudget.constant_pos a ha
  unfold dimensionConstant supportConstant
  constructor <;> nlinarith

theorem finite_quantitative (x y L : ℕ) (a K : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (ha : 0 < a) (ha₁ : a ≤ 1) (hK : 0 ≤ K)
    (hs : 64 ≤ Real.log (blockSize L)) (hl : 4 ≤ Real.log (Real.log (blockSize L)))
    (haB : 4 ≤ a * Real.log (blockSize L))
    (hn : (((mediumPrimes L (smallCutoff a L)).card + 1 : ℕ) : ℝ) ≤
      24 * blockSize L / Real.log (blockSize L))
    (hret : (pairIntersectionRank x y L : ℝ) - (2 / 3) * blockSize L * Real.log (1 / a) -
      K * (blockSize L / Real.log (blockSize L)) ≤
        ((retainedComponents x y L (smallCutoff a L) (componentCutoff L)).card : ℝ)) :
    ∃ cert : Certificate x y L,
      (pairIntersectionRank x y L : ℝ) - (2 / 3) * blockSize L * Real.log (1 / a) -
        dimensionConstant a K * (blockSize L / Real.sqrt (Real.log (blockSize L))) ≤
          (Module.finrank F₂ cert.space : ℝ) ∧
      ∀ i, ((physicalCoefficients x y L (cert.basis i).val).support.card : ℝ) ≤
        supportConstant a * (blockSize L ^ a * Real.log (blockSize L) /
          Real.log (Real.log (blockSize L))) := by
  let B := blockSize L
  let z := smallCutoff a L
  let M := componentCutoff L
  let n := (mediumPrimes L z).card + 1
  let d := branching B
  let r := radius B n
  have hBp : 0 < B := by dsimp [B, blockSize]; positivity
  have hs₀ : 0 < Real.log B := by linarith
  have hB : 1 < B := (Real.log_pos_iff hBp.le).mp hs₀
  have hl₀ : 0 < Real.log (Real.log B) := by linarith
  have hnpos : 0 < n := by dsimp [n]; omega
  have hnB := vertex_count_le_scale B n hBp.le hs hn
  have hpow := radius_power B n hs
  obtain ⟨cert, hdim, hsupport⟩ := finite_certificate x y L z M r d hx hy hpow
  have hres := residual_bound B n hs hn
  have hsmall := SmallPrimeShortBasisBudget.constraint_cost_le_large_scale B a hB ha ha₁ hs haB
  have hsprime := SmallPrimeShortBasisBudget.constraint_cost B a hB ha haB
  have hk := radius_length_bound B n hB hs hl hnpos hnB
  have hM : (M : ℝ) ≤ Real.log B := Nat.floor_le hs₀.le
  have hr : 0 < Real.sqrt (Real.log B) := Real.sqrt_pos.mpr hs₀
  have hrle : Real.sqrt (Real.log B) ≤ Real.log B := by
    have hsq := Real.sq_sqrt hs₀.le
    have hr₀ := Real.sqrt_nonneg (Real.log B)
    nlinarith
  have hscale : B / Real.log B ≤ B / Real.sqrt (Real.log B) :=
    div_le_div_of_nonneg_left hBp.le hr hrle
  have hKscale := mul_le_mul_of_nonneg_left hscale hK
  have hnat : (retainedComponents x y L z M).card ≤ Module.finrank F₂ cert.space +
      (2 * d) * n + (primeCount z + 2) := by
    change (retainedComponents x y L z M).card - (2 * d) * n - (primeCount z + 2) ≤ _ at hdim
    omega
  have hcast : ((retainedComponents x y L z M).card : ℝ) ≤
      (Module.finrank F₂ cert.space : ℝ) + (((2 * d) * n : ℕ) : ℝ) + (primeCount z : ℝ) + 2 := by
    exact_mod_cast hnat
  change (pairIntersectionRank x y L : ℝ) - (2 / 3) * B * Real.log (1 / a) -
    K * (B / Real.log B) ≤ ((retainedComponents x y L z M).card : ℝ) at hret
  change (((2 * d) * n : ℕ) : ℝ) ≤ 48 * B / Real.sqrt (Real.log B) at hres
  change (primeCount z : ℝ) + 2 ≤ SmallPrimeShortBasisBudget.constant a *
    B / Real.sqrt (Real.log B) at hsmall
  refine ⟨cert, ?_, ?_⟩
  · unfold dimensionConstant
    change (pairIntersectionRank x y L : ℝ) - (2 / 3) * B * Real.log (1 / a) -
      (K + 48 + SmallPrimeShortBasisBudget.constant a) * (B / Real.sqrt (Real.log B)) ≤ _
    simp only [div_eq_mul_inv] at hret hcast hres hsmall hKscale ⊢
    nlinarith only [hret, hcast, hres, hsmall, hKscale]
  · intro i
    have hc : ((physicalCoefficients x y L (cert.basis i).val).support.card : ℝ) ≤
        (M : ℝ) * ((2 * r + 1 : ℕ) : ℝ) * ((primeCount z : ℝ) + 3) := by
      exact_mod_cast hsupport i
    have hc₀ := (SmallPrimeShortBasisBudget.constant_pos a ha).le
    have hstep : (M : ℝ) * ((2 * r + 1 : ℕ) : ℝ) * ((primeCount z : ℝ) + 3) ≤
        (Real.log B * (11 * Real.log B / Real.log (Real.log B))) *
          (SmallPrimeShortBasisBudget.constant a * B ^ a / Real.log B) :=
      mul_le_mul (mul_le_mul hM hk (by positivity) hs₀.le) hsprime (by positivity) (by positivity)
    refine hc.trans (hstep.trans_eq ?_)
    unfold supportConstant
    change (Real.log B * (11 * Real.log B / Real.log (Real.log B))) *
      (SmallPrimeShortBasisBudget.constant a * B ^ a / Real.log B) =
        (11 * SmallPrimeShortBasisBudget.constant a) * (B ^ a * Real.log B / Real.log (Real.log B))
    field_simp

theorem article_13_1 (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ KD KS : ℝ, 0 < KD ∧ 0 < KS ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ PaperP1.Model.dyadicBlock N, ∀ y ∈ PaperP1.Model.dyadicBlock N,
      ∃ cert : Certificate x y L,
        (pairIntersectionRank x y L : ℝ) - (2 / 3) * blockSize L * Real.log (1 / a) -
          KD * (blockSize L / Real.sqrt (Real.log (blockSize L))) ≤
            (Module.finrank F₂ cert.space : ℝ) ∧
        (∀ i, ((physicalCoefficients x y L (cert.basis i).val).support.card : ℝ) ≤
          KS * (blockSize L ^ a * Real.log (blockSize L) / Real.log (Real.log (blockSize L)))) ∧
        ∀ w : cert.space, w ≠ 0 →
          (selected (firstPhysical x y L w.val)).Nonempty ∧
          Even (selected (firstPhysical x y L w.val)).card ∧
          (selected (secondPhysical x y L w.val)).Nonempty ∧
          Even (selected (secondPhysical x y L w.val)).card ∧ commonClasses x y L w.val ≠ 0 := by
  obtain ⟨K, hK, hretained⟩ := critical_retained_lower a ha ha₁
  obtain ⟨Bparam, hparam⟩ := logarithmic_threshold a ha
  obtain ⟨Bprime, _hBprime, hprime⟩ := ComponentPrimeBudget.prime_constraint_cost_eventually
  let B₀ := max Bparam Bprime
  obtain ⟨hKD, hKS⟩ := constants_pos a K ha hK.le
  refine ⟨dimensionConstant a K, supportConstant a, hKD, hKS, ?_⟩
  intro C
  obtain ⟨Nret, hNret⟩ := hretained C
  obtain ⟨Nscale, hNscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((B₀ : ℝ) / lowerScale)))
  refine ⟨max 2 (max Nret (max Nscale Nlog)), ?_⟩
  intro N hN L hband x hx y hy
  have hblog : (B₀ : ℝ) ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp (hNlog N (by omega))
    nlinarith
  have hBreal : (B₀ : ℝ) ≤ blockSize L := hblog.trans (hNscale N (by omega) L hband).1
  have hBnat : B₀ ≤ L + 1 := by
    change (B₀ : ℝ) ≤ ((L + 1 : ℕ) : ℝ) at hBreal
    exact_mod_cast hBreal
  obtain ⟨_hBtwo, hs, hl, haB⟩ := hparam (L + 1) ((le_max_left _ _).trans hBnat)
  have hp := hprime (L + 1) ((le_max_right _ _).trans hBnat)
  change (primeCount (10 * (L + 1)) : ℝ) + 4 ≤
    24 * blockSize L / Real.log (blockSize L) at hp
  have hmedium : ((mediumPrimes L (smallCutoff a L)).card : ℝ) ≤
      (primeCount (10 * (L + 1)) : ℝ) := by
    exact_mod_cast medium_card_le_primeCount L (smallCutoff a L)
  have hn : (((mediumPrimes L (smallCutoff a L)).card + 1 : ℕ) : ℝ) ≤
      24 * blockSize L / Real.log (blockSize L) := by
    push_cast
    linarith
  have hxpos : 1 ≤ x := by have h := (mem_Ico.mp hx).1; omega
  have hypos : 1 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  obtain ⟨cert, hdim, hsupport⟩ := finite_quantitative x y L a K hxpos hypos ha ha₁ hK.le
    hs hl haB hn (hNret N (by omega) L hband x hx y hy)
  exact ⟨cert, hdim, hsupport, fun w hw ↦ nonzero_even_selections x y L cert w hw⟩

end PaperP1.ShortBasisTheorem
