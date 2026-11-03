module

public import PaperP1.Asymptotics.PrimitiveFourModerateMass
public import PaperP1.Asymptotics.RestrictedDensePrimitiveMassUnderInputs
public import PaperP1.Asymptotics.MultiAnchorSaturationDegrees
public import PaperP1.Asymptotics.SmallKernelWindows
public import PaperP1.Model.PrimitiveRareWindows
public import PaperP1.Combinatorics.TwoSourcePopulations

/-! # The sharp four-block dense primitive mass from four actual arithmetic sectors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveFourMassUnderInputs

open Finset Filter PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.ConnectedWindowFamilies
  PaperP1.DensePrimitiveTripleMassUnderInputs PaperP1.PrimitiveSmallKernelDichotomy
  PaperP1.TwoSourcePopulations

theorem uniform_bound (C η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 4 ∧ Primitive L I ∧
        η * L ≤ (runRelativeNullity L I : ℝ)) →
      mass F L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε) := by
  classical
  let δ := ε / 8
  let σ := (5 : ℝ) / 3 + 2 * δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨p, hp⟩ := RestrictedDensePrimitiveMassUnderInputs.uniform_bound 2 (by norm_num)
    C η σ (ε / 4) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := PrimitiveFourModerateMass.uniform_bound C (ε / 2) (by positivity)
  obtain ⟨NB, _hNB, hb⟩ := TwoSmallKernelWindowUpper.critical_upper (2 / 3) C δ hδ
  obtain ⟨NR, hr⟩ := SmallKernelWindows.critical_several_count 11 6 (9 / 10) (2 / 3) C δ
    (by norm_num) (by norm_num) (by norm_num) hδ
  obtain ⟨NS, hs⟩ := MultiAnchorSaturationDegrees.uniform_degrees 4 C 6 δ
    (by norm_num) (by norm_num) hδ
  obtain ⟨NG, hg⟩ := SaturationDegrees.finite_conditions C 6 (by norm_num)
  obtain ⟨NX, hxscale⟩ := HalfCountSchedule.factor_absorption 3 0 (1 / 3) (by norm_num)
  obtain ⟨NL, hl⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop ((C + 15 / η) * Real.log 2)))
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 4 (-(4 : ℝ) / 3 + ε / 2)
    (ε / 2) (by positivity)
  refine ⟨p, ?_⟩
  intro hgeo
  obtain ⟨ND, _hND, hd⟩ := hp hgeo
  refine ⟨10 + NM + NB + NR + NS + NG + NX + NL + NA + ND, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let Y := PaperP1.MultiAnchorOrder.cutoff 6 N
  let T := (N : ℝ) ^ (9 / 10 : ℝ)
  let Bad := TwoSmallKernelWindows.windows N L (L + 1) ((N : ℝ) ^ (2 / 3 : ℝ))
  let Rare := SmallKernelWindowSets.severalWindows N L ⌊Y⌋₊ 11 (9 / 10) (2 / 3)
  let P := fun I : Finset ℕ ↦ FixedOrderAnchorMass.Covered 4 4 (L + 1) N Y T I
  let Q := fun I : Finset ℕ ↦ SaturatedPair 4 L N Y I
  let R := fun I : Finset ℕ ↦ ∃ x ∈ I, x ∈ Bad
  let FM := F.filter P
  let FU := F.filter fun I ↦ ¬ P I
  let FS := FU.filter Q
  let FV := FU.filter fun I ↦ ¬ Q I
  let FB := FV.filter R
  let FR := FV.filter fun I ↦ ¬ R I
  have hFS (I : Finset ℕ) (hI : I ∈ FS) : I ∈ F := (mem_filter.mp (mem_filter.mp hI).1).1
  have hFB (I : Finset ℕ) (hI : I ∈ FB) : I ∈ F :=
    (mem_filter.mp (mem_filter.mp (mem_filter.mp hI).1).1).1
  have hFR (I : Finset ℕ) (hI : I ∈ FR) : I ∈ F :=
    (mem_filter.mp (mem_filter.mp (mem_filter.mp hI).1).1).1
  have hsplit : mass F L = mass FM L + mass FS L + mass FB L + mass FR L := by
    have h₁ := sum_filter_add_sum_filter_not F P (weight L)
    have h₂ := sum_filter_add_sum_filter_not FU Q (weight L)
    have h₃ := sum_filter_add_sum_filter_not FV R (weight L)
    change mass FM L + mass FU L = mass F L at h₁
    change mass FS L + mass FV L = mass FU L at h₂
    change mass FB L + mass FR L = mass FV L at h₃
    linarith only [h₁, h₂, h₃]
  have hmoderate : mass FM L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    apply (hm N (by omega) L hband FM ?_).trans
    · apply Real.rpow_le_rpow_of_exponent_le hn1
      linarith
    · intro I hI
      obtain ⟨hIF, hP⟩ := mem_filter.mp hI
      exact ⟨(hF I hIF).1, (hF I hIF).2.1, (hF I hIF).2.2.1, hP⟩
  have hrestricted (S U : Finset (Finset ℕ)) (hU : U ⊆ F)
      (hS : ∀ E ∈ S, E ⊆ dyadicBlock N ∧ E.card = 2)
      (hcard : (S.card : ℝ) ≤ (N : ℝ) ^ σ)
      (hcover : ∀ I ∈ U, ∃ E ∈ S, E ⊆ I) :
      mass U L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    have h := hd N (by omega) L hband S U hS hcard
      (fun I hI ↦ hF I (hU hI)) hcover
    have heq : -(3 : ℝ) + σ + ε / 4 = -(4 : ℝ) / 3 + ε / 2 := by dsimp [σ, δ]; ring
    norm_num only [Nat.cast_ofNat] at h
    rw [heq] at h
    exact h
  have hpaircard : ((saturatedPairs 4 L N Y).card : ℝ) ≤ (N : ℝ) ^ σ := by
    have hdegree : ∀ x ∈ dyadicBlock N,
        ((PaperP1.MultiAnchorSaturation.outgoing 4 (L + 1) N Y x).card : ℝ) ≤
          (N : ℝ) ^ ((4 : ℝ) / 6 + δ) := fun x hx ↦ (hs N (by omega) L hband).1 x hx |>.1
    calc
      _ ≤ N * (N : ℝ) ^ ((4 : ℝ) / 6 + δ) := saturated_card 4 L N Y _ hdegree
      _ = (N : ℝ) ^ (1 + ((4 : ℝ) / 6 + δ)) := by conv_rhs => rw [Real.rpow_add hn, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [σ]; linarith)
  have hsaturated : mass FS L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    apply hrestricted (saturatedPairs 4 L N Y) FS (fun I hI ↦ hFS I hI)
      (fun E hE ↦ saturated_properties hE) hpaircard
    intro I hI
    exact saturated_cover (hF I (hFS I hI)).1 (mem_filter.mp hI).2
  have hbad : (Bad.card : ℝ) ≤ (N : ℝ) ^ ((2 : ℝ) / 3 + δ) := by
    simpa only [Bad, max_self] using hb N (by omega) L hband
  have hbadcard : ((markedPairs Bad (dyadicBlock N)).card : ℝ) ≤ (N : ℝ) ^ σ := by
    calc
      _ ≤ (Bad.card : ℝ) * (dyadicBlock N).card := by exact_mod_cast marked_card Bad (dyadicBlock N)
      _ = (Bad.card : ℝ) * N := by rw [dyadicBlock_card]
      _ ≤ (N : ℝ) ^ ((2 : ℝ) / 3 + δ) * N := mul_le_mul_of_nonneg_right hbad hn.le
      _ = (N : ℝ) ^ (((2 : ℝ) / 3 + δ) + 1) := by
        have h := Real.rpow_add hn ((2 : ℝ) / 3 + δ) 1
        rw [Real.rpow_one] at h
        exact h.symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [σ]; linarith)
  have hbadmass : mass FB L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    apply hrestricted (markedPairs Bad (dyadicBlock N)) FB (fun I hI ↦ hFB I hI)
      (fun E hE ↦ marked_properties (filter_subset _ _) hE) hbadcard
    intro I hI
    exact marked_cover (hF I (hFB I hI)).1 (by rw [(hF I (hFB I hI)).2.1]; omega)
      (mem_filter.mp hI).2
  have hrare : (Rare.card : ℝ) ≤ (N : ℝ) ^ ((5 : ℝ) / 6 + δ) := by
    have h := hr N (by omega) L hband
    norm_num only at h
    simpa only [Rare, Y, PaperP1.MultiAnchorOrder.cutoff, PaperP1.ModerateOrder.cutoff, max_self] using h
  have hrarecard : ((Rare.powersetCard 2).card : ℝ) ≤ (N : ℝ) ^ σ := by
    calc
      _ ≤ (Rare.card : ℝ) ^ 2 := by exact_mod_cast pair_card Rare
      _ ≤ ((N : ℝ) ^ ((5 : ℝ) / 6 + δ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hrare 2
      _ = (N : ℝ) ^ σ := by
        rw [← Real.rpow_mul_natCast hn.le]
        congr 1
        dsimp [σ]
        ring
  obtain ⟨_hN10, _hB, hBN, hY, _hwidth⟩ := hg N (by omega) L hband
  have hscale : (3 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hxscale N (by omega)
  have hlength : (15 : ℝ) ≤ η * L := by
    have hlog : C + 15 / η ≤ Real.log N / Real.log 2 :=
      (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr (hl N (by omega))
    have hL : 15 / η ≤ (L : ℝ) := by have h := (abs_le.mp hband).1; linarith
    have h := (div_le_iff₀ hη).mp hL
    linarith
  have hrarecover (I : Finset ℕ) (hI : I ∈ FR) : I ⊆ Rare := by
    obtain ⟨hIV, hnotR⟩ := mem_filter.mp hI
    obtain ⟨hIU, hnotQ⟩ := mem_filter.mp hIV
    obtain ⟨hIF, hnotP⟩ := mem_filter.mp hIU
    intro x hx
    have hsparse := PrimitiveSmallKernelDichotomy.primitive_nullity (by omega : 2 ≤ N)
      I (hF I hIF).2.1 (hF I hIF).1 Y T hY (hF I hIF).2.2.1 hnotP hnotQ ⟨x, hx⟩
    change runRelativeNullity L I ≤ (smallOffsets L Y T x).card + 3 at hsparse
    have hdense : 15 ≤ runRelativeNullity L I := by exact_mod_cast hlength.trans (hF I hIF).2.2.2
    exact PrimitiveRareWindows.many_small_values (by omega) (by omega) hscale ((hF I hIF).1 hx)
      Y (9 / 10) (by dsimp [Y, PaperP1.MultiAnchorOrder.cutoff, PaperP1.ModerateOrder.cutoff]; positivity)
      (by change 12 ≤ (smallOffsets L Y T x).card; omega)
      (fun hxB ↦ hnotR ⟨x, hx, hxB⟩)
  have hraremass : mass FR L ≤ (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
    apply hrestricted (Rare.powersetCard 2) FR (fun I hI ↦ hFR I hI)
      (fun E hE ↦ ⟨(mem_powersetCard.mp hE).1.trans (filter_subset _ _), (mem_powersetCard.mp hE).2⟩)
      hrarecard
    intro I hI
    exact pair_cover (hrarecover I hI) (by rw [(hF I (hFR I hI)).2.1]; omega)
  calc
    _ = mass FM L + mass FS L + mass FB L + mass FR L := hsplit
    _ ≤ 4 * (N : ℝ) ^ (-(4 : ℝ) / 3 + ε / 2) := by
      linarith only [hmoderate, hsaturated, hbadmass, hraremass]
    _ ≤ (N : ℝ) ^ ((-(4 : ℝ) / 3 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePrimitiveFourMassUnderInputs
