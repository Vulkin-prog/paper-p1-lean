module

public import PaperP1.Asymptotics.SlowPrimeBandSieve
public import PaperP1.Analysis.CountWeightedSum

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FlexiblePrimeBandSieve
open Finset Filter PaperP1 PrimeAvoidanceSieve
open scoped Classical

def band (L U : ℕ → ℝ) (N : ℕ) : Finset ℕ := (Ioc ⌊L N⌋₊ ⌊U N⌋₊).filter Nat.Prime

theorem reciprocal_mass_tendsto (L U : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgeom : ∀ᶠ N in atTop, 2 ≤ L N ∧ L N ≤ U N)
    (hgap : Tendsto (fun N ↦ Real.log (Real.log (U N))-Real.log (Real.log (L N))) atTop atTop) :
    Tendsto (fun N ↦ reciprocalMass (band L U N)) atTop atTop := by
  have hloglow := Real.tendsto_log_atTop.comp hL
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hgeom,hloglow.eventually (eventually_ge_atTop (2*PrimeLogMertens.budget+1)),
    hgap.eventually (eventually_ge_atTop (b+1))] with N hg hden hgapN
  change 2*PrimeLogMertens.budget+1 ≤ Real.log (L N) at hden
  have hlog : 0 < Real.log (L N) := Real.log_pos (by linarith [hg.1])
  have he := PrimeHarmonicWindow.finite_window_bound (L N) (U N) hg.1 hg.2
  have herr : 2*PrimeLogMertens.budget/Real.log (L N) ≤ 1 :=
    (div_le_iff₀ hlog).mpr (by linarith)
  have hlo := (abs_le.mp (he.trans herr)).1
  change -(1 : ℝ) ≤ reciprocalMass (band L U N)-
    (Real.log (Real.log (U N))-Real.log (Real.log (L N))) at hlo
  linarith

theorem card_bound (L U : ℕ → ℝ) (N : ℕ) : (band L U N).card ≤ ⌊U N⌋₊ := by
  have hs : band L U N ⊆ Ioc 0 ⌊U N⌋₊ := by
    intro p hp
    obtain ⟨hpint,hprime⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨hprime.pos,(mem_Ioc.mp hpint).2⟩
  simpa only [Nat.card_Ioc,Nat.sub_zero] using card_le_card hs

theorem normalized_card_square_tendsto (L U : ℕ → ℝ)
    (hU : ∀ᶠ N in atTop, 0 ≤ U N)
    (hsmall : Tendsto (fun N : ℕ ↦ (U N)^2/(N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ ((band L U N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [hU] with N hu
    have hc : ((band L U N).card : ℝ) ≤ U N :=
      (by exact_mod_cast card_bound L U N : ((band L U N).card : ℝ) ≤ (⌊U N⌋₊ : ℝ)).trans (Nat.floor_le hu)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) (Nat.cast_nonneg _)

theorem avoidance_density_tendsto (P : ℕ → Finset ℕ) (hP : ∀ N p, p ∈ P N → p.Prime)
    (hH : Tendsto (fun N ↦ reciprocalMass (P N)) atTop atTop)
    (hcard : Tendsto (fun N : ℕ ↦ ((P N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ ((avoiding (P N) (2*N)).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun N ↦ (reciprocalMass (P N))⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hH
  have hb : Tendsto (fun N : ℕ ↦ 2/reciprocalMass (P N)+
      (((P N).card : ℝ)^2/(N : ℝ))*(reciprocalMass (P N))⁻¹^2) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,add_zero,zero_pow (by norm_num : 2 ≠ 0)] using
      (hi.const_mul 2).add (hcard.mul (hi.pow 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [hH.eventually (eventually_ge_atTop 1),eventually_ge_atTop 1] with N hmass hN
    have hHp : 0 < reciprocalMass (P N) := by linarith
    have hc := avoidance_card (P N) (hP N) (2*N) hHp
    have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have he : (((2*N : ℕ) : ℝ)/reciprocalMass (P N)+
        ((P N).card : ℝ)^2/(reciprocalMass (P N))^2)/(N : ℝ) =
        2/reciprocalMass (P N)+(((P N).card : ℝ)^2/(N : ℝ))*(reciprocalMass (P N))⁻¹^2 := by
      push_cast
      field_simp
    exact hh.trans_eq he

theorem square_density_tendsto (L U : ℕ → ℝ) (hL : Tendsto L atTop atTop) :
    Tendsto (fun N : ℕ ↦ ((PrimeDivisorWeights.squareExceptions (band L U N) (2*N)).card : ℝ)/(N : ℝ))
      atTop (nhds 0) := by
  have hb : Tendsto (fun N ↦ 4/L N) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using (tendsto_inv_atTop_zero.comp hL).const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [hL.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with N hl hN
    have hc := CountWeightedSum.square_count_bound (band L U N) (2*N) (L N) hl (by
      intro p hp
      exact (Nat.floor_lt (by linarith : 0 ≤ L N)).mp (mem_Ioc.mp (mem_filter.mp hp).1).1)
    have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have he : (2*((2*N : ℕ) : ℝ)/L N)/(N : ℝ)=4/L N := by push_cast; field_simp; norm_num
    exact hh.trans_eq he

def excluded (L U : ℕ → ℝ) (N : ℕ) : Finset ℕ :=
  avoiding (band L U N) (2*N) ∪ PrimeDivisorWeights.squareExceptions (band L U N) (2*N)

def good (L U : ℕ → ℝ) (N : ℕ) : Finset ℕ := Ico N (2*N) \ excluded L U N

theorem excluded_density_tendsto (L U : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgeom : ∀ᶠ N in atTop, 2 ≤ L N ∧ L N ≤ U N)
    (hgap : Tendsto (fun N ↦ Real.log (Real.log (U N))-Real.log (Real.log (L N))) atTop atTop)
    (hsmall : Tendsto (fun N : ℕ ↦ (U N)^2/(N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ ((excluded L U N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hm := reciprocal_mass_tendsto L U hL hgeom hgap
  have hu : ∀ᶠ N in atTop, 0 ≤ U N := hgeom.mono (fun _ hg ↦ by linarith [hg.1,hg.2])
  have hc := normalized_card_square_tendsto L U hu hsmall
  have ha := avoidance_density_tendsto (band L U) (fun _N _p hp ↦ (mem_filter.mp hp).2) hm hc
  have hs := square_density_tendsto L U hL
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [add_zero] using ha.add hs)
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have hh : ((excluded L U N).card : ℝ) ≤ ((avoiding (band L U N) (2*N)).card : ℝ)+
        ((PrimeDivisorWeights.squareExceptions (band L U N) (2*N)).card : ℝ) := by
      exact_mod_cast card_union_le _ _
    simpa only [add_div] using div_le_div_of_nonneg_right hh (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem good_support (L U : ℕ → ℝ) (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ good L U N) :
    (0 < n ∧ n ≤ 2*N) ∧ 0 < PrimeDivisorWeights.count (band L U N) n ∧
      ∀ p ∈ band L U N, ¬p^2 ∣ n := by
  have hni := mem_Ico.mp (mem_sdiff.mp hn).1
  have hne := (mem_sdiff.mp hn).2
  have hn0 : 0 < n := hN.trans_le hni.1
  have hnX : n ≤ 2*N := hni.2.le
  refine ⟨⟨hn0,hnX⟩,?_,?_⟩
  · by_contra hcount
    apply hne
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨hn0,hnX⟩,?_⟩
    intro p hp hpn
    have hpos := PrimeDivisorWeights.count_pos hp hpn
    omega
  · intro p hp hsq
    apply hne
    apply mem_union_right
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn0,hnX⟩,⟨p,hp,hsq⟩⟩

theorem missing_good_density_tendsto (L U : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hgeom : ∀ᶠ N in atTop, 2 ≤ L N ∧ L N ≤ U N)
    (hgap : Tendsto (fun N ↦ Real.log (Real.log (U N))-Real.log (Real.log (L N))) atTop atTop)
    (hsmall : Tendsto (fun N : ℕ ↦ (U N)^2/(N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ good L U N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (excluded_density_tendsto L U hL hgeom hgap hsmall)
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have hs : Ico N (2*N) \ good L U N ⊆ excluded L U N := by
      intro n hn
      by_contra hnot
      exact (mem_sdiff.mp hn).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hn).1,hnot⟩)
    have hc : ((Ico N (2*N) \ good L U N).card : ℝ) ≤ (excluded L U N).card := by exact_mod_cast card_le_card hs
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
end PaperP1.FlexiblePrimeBandSieve
