module

public import PaperP1.Model.SupportedPrimeCylinder

/-! # Exact valuation condition for the retained positive starts
The preceding value at q*u is negative exactly when the q-adic
valuation of the positive multiplier u is even. Coprimality is a
sufficient special case. The same supported cylinder therefore forces
a larger explicitly defined set of positive starts.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.ValuationPrimeCylinder

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Algebra PaperP1.Probability
  PaperP1.LocalDefectBound

def retainedParameters (N q : ℕ) : Finset ℕ :=
  (PrimeRunStarts.parameters N q).filter fun u ↦ parityVec u q=0

def starts (N q : ℕ) : Finset ℕ := (retainedParameters N q).image fun u ↦ q*u+1

theorem mem_starts (N q x : ℕ) : x∈starts N q ↔
    ∃ u∈PrimeRunStarts.parameters N q, parityVec u q=0 ∧ q*u+1=x := by
  simp only [starts,mem_image,retainedParameters,mem_filter]
  constructor
  · rintro ⟨u,⟨hu,hbit⟩,hx⟩
    exact ⟨u,hu,hbit,hx⟩
  · rintro ⟨u,hu,hbit,hx⟩
    exact ⟨u,⟨hu,hbit⟩,hx⟩

theorem parity_condition_iff_even (q u : ℕ) : parityVec u q=0 ↔ Even (u.factorization q) := by
  rw [parityVec_apply]
  exact ZMod.natCast_eq_zero_iff_even

theorem positive_start_iff {M : ℕ} (q : PrimeUpTo M) (u : ℕ) (hu : 0<u) :
    (StartEvent (valueBit (OneNegativePrime.sample q)) (q.val.val*u+1) (q.val.val-1) ∧
      valueBit (OneNegativePrime.sample q) (q.val.val*u+1)=0) ↔ parityVec u q.val.val=0 := by
  let p : ℕ := q.val.val
  change (StartEvent (valueBit (OneNegativePrime.sample q)) (p*u+1) (p-1) ∧
    valueBit (OneNegativePrime.sample q) (p*u+1)=0) ↔ parityVec u p=0
  have hp : Nat.Prime p := q.property
  have hp2 : 2≤p := hp.two_le
  have hprev : valueBit (OneNegativePrime.sample q) (p*u+1-1)=1+parityVec u p := by
    rw [Nat.add_sub_cancel,OneNegativePrime.valueBit_sample]
    change parityVec (p*u) p=1+parityVec u p
    rw [parityVec_mul hp.ne_zero hu.ne']
    simp only [Finsupp.add_apply,parityVec_apply,hp.factorization_self,Nat.cast_one]
  have hinside (j : ℕ) (hj : j<p-1) : valueBit (OneNegativePrime.sample q) (p*u+1+j)=0 := by
    rw [OneNegativePrime.valueBit_sample]
    have heq : p*u+1+j=p*u+(j+1) := by omega
    rw [heq]
    exact OneNegativePrime.parity_zero_of_not_dvd
      (OneNegativePrime.not_dvd_inside (by omega) (by omega))
  have hfirst := hinside 0 (by omega)
  simp only [Nat.add_zero] at hfirst
  constructor
  · rintro ⟨⟨hstart,_⟩,_⟩
    rw [hprev,hfirst,add_zero] at hstart
    exact add_left_cancel (show (1 : F₂)+parityVec u p=1+0 by simpa only [add_zero] using hstart)
  · intro hbit
    refine ⟨⟨?_,fun j hj ↦ ?_⟩,hfirst⟩
    · simp only [hprev,hfirst,hbit,add_zero]
    · rw [hinside j hj,hfirst]

theorem positive_start_iff_even_factorization {M : ℕ} (q : PrimeUpTo M) (u : ℕ) (hu : 0<u) :
    (StartEvent (valueBit (OneNegativePrime.sample q)) (q.val.val*u+1) (q.val.val-1) ∧
      valueBit (OneNegativePrime.sample q) (q.val.val*u+1)=0) ↔ Even (u.factorization q.val.val) :=
  (positive_start_iff q u hu).trans (parity_condition_iff_even q.val.val u)

theorem original_starts_subset (N q : ℕ) : OneSidedPrimeCylinder.starts N q⊆starts N q := by
  intro x hx
  obtain ⟨u,hu,hnot,rfl⟩ := (OneSidedPrimeCylinder.mem_starts N q x).mp hx
  exact (mem_starts N q _).mpr ⟨u,hu,OneNegativePrime.parity_zero_of_not_dvd hnot,rfl⟩

theorem retained_starts_cutoff {N q : ℕ} (hq : 2≤q) (hqN : q≤N) :
    ∀ x∈starts N q, x+(q-1)≤SupportedPrimeCylinder.cutoff N q := by
  intro x hx
  obtain ⟨u,hu,_hbit,rfl⟩ := (mem_starts N q x).mp hx
  have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le (by omega : 0<q)).mpr
    (by simpa only [one_mul] using hqN)
  obtain ⟨_hlo,hhi⟩ := mem_Ico.mp hu
  have huHi : u+1≤2*(N/q) := by omega
  have hmul := Nat.mul_le_mul_left q huHi
  have hsub : q-1+1=q := by omega
  unfold SupportedPrimeCylinder.cutoff
  nlinarith

theorem starts_subset_interval {N q : ℕ} (hq : 2≤q) (hqN : q≤N) :
    starts N q⊆dyadicBlock N := by
  intro x hx
  have hcut := (retained_starts_cutoff hq hqN x hx).trans
    (SupportedPrimeCylinder.cutoff_le_two_mul N q)
  obtain ⟨u,hu,_hbit,rfl⟩ := (mem_starts N q x).mp hx
  have hlo := (mem_Ico.mp hu).1
  have hmul := Nat.mul_le_mul_left q hlo
  have hmod := Nat.mod_add_div N q
  have hmodlt := Nat.mod_lt N (by omega : 0<q)
  have hlength : 1≤q-1 := by omega
  apply mem_Ico.mpr
  constructor <;> nlinarith

theorem positive_count_on_sample {M N : ℕ} (q : PrimeUpTo M) :
    (starts N q.val.val).card≤ indicatorCount (starts N q.val.val)
      (fun x ↦ PositiveStarts.indicator x (q.val.val-1)) (OneNegativePrime.sample q) := by
  rw [← card_activeSites]
  apply card_le_card
  intro x hx
  obtain ⟨u,hu,hbit,heq⟩ := (mem_starts N q.val.val x).mp hx
  have huPos : 0<u := (Nat.zero_lt_succ _).trans_le ((mem_Ico.mp hu).1)
  have hstart := (positive_start_iff q u huPos).mpr hbit
  apply mem_filter.mpr
  refine ⟨hx,?_⟩
  rw [← heq]
  simp only [PositiveStarts.indicator,Bool.and_eq_true,decide_eq_true_eq,startIndicator_eq_true_iff]
  exact hstart

theorem positive_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((starts N q).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  let M := SupportedPrimeCylinder.cutoff N q
  let p : PrimeUpTo M := ⟨⟨q,by
    have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le hq.pos).mpr (by simpa only [one_mul] using hqN)
    have hmul := Nat.mul_le_mul_left (2*q) hdiv
    dsimp [M,SupportedPrimeCylinder.cutoff]
    nlinarith⟩,hq⟩
  let σ := OneNegativePrime.sample p
  let G := starts N q
  have hcount := positive_count_on_sample (N:=N) p
  have hcountR : (G.card : ℝ)≤
      (indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ) := by exact_mod_cast hcount
  have hatom := PrimeRunCylinder.finiteExpectation_ge_atom (cylinderProbability M)
    (fun σ ↦ Real.exp (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ)))
      (fun _ ↦ (Real.exp_pos _).le) σ
  have hrestricted : Real.exp (t*(G.card : ℝ)-(primeCount M : ℝ)*Real.log 2)≤
      PositiveStarts.exponentialMoment G (q-1) t := by
    rw [SupportedPrimeCylinder.positive_moment_eq_finite (retained_starts_cutoff hq.two_le hqN)]
    calc
      _ = (cylinderProbability M).weight σ*Real.exp (t*(G.card : ℝ)) := by
        rw [PrimeCylinderSize.atom_weight,Real.exp_sub,Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ)<2)]
        ring
      _ ≤ (cylinderProbability M).weight σ*Real.exp
          (t*(indicatorCount G (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcountR ht))
          ((cylinderProbability M).weight_nonneg σ)
      _ ≤ _ := hatom
  exact hrestricted.trans (SupportedPrimeCylinder.positive_moment_mono
    (starts_subset_interval hq.two_le hqN) (q-1) t ht)

theorem total_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*((starts N q).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_card_lower hq hqN t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem starts_card_lower {N q : ℕ} (hq : 2≤q) (hqN : q≤N) :
    (N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3≤(starts N q).card := by
  exact (OneSidedPrimeCylinder.starts_card_lower hq hqN).trans
    (by exact_mod_cast card_le_card (original_starts_subset N q))

theorem new_start_example : 28∈starts 18 3 := by
  apply (mem_starts 18 3 28).mpr
  refine ⟨9,by norm_num [PrimeRunStarts.parameters],?_,by norm_num⟩
  change parityVec (3^2) 3=0
  rw [parityVec_pow_two,Finsupp.zero_apply]

theorem excluded_by_previous_example : 28∉OneSidedPrimeCylinder.starts 18 3 := by
  intro hx
  obtain ⟨u,_hu,hnot,heq⟩ := (OneSidedPrimeCylinder.mem_starts 18 3 28).mp hx
  have hu : u=9 := by omega
  subst u
  norm_num at hnot

theorem strictly_more_starts_example :
    (OneSidedPrimeCylinder.starts 18 3).card<(starts 18 3).card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨original_starts_subset 18 3,?_⟩
  intro heq
  exact excluded_by_previous_example (heq.symm ▸ new_start_example)

theorem strictly_stronger_card_bound_example (t : ℝ) (ht : 0<t) :
    Real.exp (t*((OneSidedPrimeCylinder.starts 18 3).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff 18 3) : ℝ)*Real.log 2)<
    Real.exp (t*((starts 18 3).card : ℝ)-
      (primeCount (SupportedPrimeCylinder.cutoff 18 3) : ℝ)*Real.log 2) := by
  apply Real.exp_lt_exp.mpr
  exact sub_lt_sub_right (mul_lt_mul_of_pos_left
    (by exact_mod_cast strictly_more_starts_example) ht) _

end PaperP1.ValuationPrimeCylinder
