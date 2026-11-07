module

public import PaperP1.Model.PrimeRunCylinder

/-! # A one-sided count in the one-negative-prime cylinder

A run start of length at least q-1 only needs the preceding negative value
and the following q-1 positive values. The sign immediately after that word
is unrestricted. Thus only q | u is excluded among starts q*u+1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.OneSidedPrimeCylinder

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Algebra PaperP1.Probability
  PaperP1.LocalDefectBound

def retainedParameters (N q : ℕ) : Finset ℕ :=
  (PrimeRunStarts.parameters N q).filter fun u ↦ ¬q ∣ u

def starts (N q : ℕ) : Finset ℕ :=
  (retainedParameters N q).image fun u ↦ q*u+1

theorem mem_starts (N q x : ℕ) : x ∈ starts N q ↔
    ∃ u ∈ PrimeRunStarts.parameters N q, ¬q ∣ u ∧ q*u+1=x := by
  simp only [starts, mem_image, retainedParameters, mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hq⟩, hx⟩
    exact ⟨u, hu, hq, hx⟩
  · rintro ⟨u, hu, hq, hx⟩
    exact ⟨u, ⟨hu, hq⟩, hx⟩

theorem original_starts_subset (N q : ℕ) : PrimeRunStarts.starts N q ⊆ starts N q := by
  intro x hx
  obtain ⟨u, hu, hnot, _hnext, heq⟩ := (PrimeRunStarts.mem_starts N q x).mp hx
  exact (mem_starts N q x).mpr ⟨u, hu, hnot, heq⟩

theorem positive_start {M : ℕ} (q : PrimeUpTo M) (u : ℕ) (hu : ¬q.val.val ∣ u) :
    StartEvent (valueBit (OneNegativePrime.sample q)) (q.val.val*u+1) (q.val.val-1) ∧
      valueBit (OneNegativePrime.sample q) (q.val.val*u+1)=0 := by
  let p : ℕ := q.val.val
  have hp : Nat.Prime p := q.property
  have hp2 : 2 ≤ p := hp.two_le
  have hprev : valueBit (OneNegativePrime.sample q) (p*u+1-1)=1 := by
    rw [Nat.add_sub_cancel, OneNegativePrime.valueBit_sample]
    exact OneNegativePrime.parity_simple_multiple hp hu
  have hinside (j : ℕ) (hj : j<p-1) :
      valueBit (OneNegativePrime.sample q) (p*u+1+j)=0 := by
    rw [OneNegativePrime.valueBit_sample]
    have heq : p*u+1+j=p*u+(j+1) := by omega
    rw [heq]
    exact OneNegativePrime.parity_zero_of_not_dvd
      (OneNegativePrime.not_dvd_inside (by omega) (by omega))
  have hfirst := hinside 0 (by omega)
  simp only [Nat.add_zero] at hfirst
  refine ⟨⟨?_, ?_⟩, hfirst⟩
  · rw [hprev, hfirst, add_zero]
  · intro j hj
    rw [hinside j hj, hfirst]

theorem starts_subset_interval {N q : ℕ} (hq : 2 ≤ q) (hqN : q ≤ N) :
    starts N q ⊆ Ico N (2*N) := by
  intro x hx
  obtain ⟨u, hu, _hu, rfl⟩ := (mem_starts N q x).mp hx
  have hqpos : 0<q := by omega
  have hdiv : 1 ≤ N/q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
  obtain ⟨huLo, huHi⟩ := mem_Ico.mp hu
  have hlo := Nat.mul_le_mul_left q huLo
  have hhi := Nat.mul_le_mul_left q (show u+1 ≤ 2*(N/q) by omega)
  have hmod := Nat.mod_add_div N q
  have hmodlt := Nat.mod_lt N hqpos
  have hdivle := Nat.div_mul_le_self N q
  rw [Nat.mul_add, Nat.mul_one] at hlo hhi
  exact mem_Ico.mpr ⟨by nlinarith, by nlinarith⟩

theorem retainedParameters_card_lower (N q : ℕ) :
    N/q-1 ≤ (retainedParameters N q).card+((N/q-1)/q+1) := by
  let bad := (PrimeRunStarts.parameters N q).filter fun u ↦ q ∣ u
  have hcover : PrimeRunStarts.parameters N q ⊆ retainedParameters N q ∪ bad := by
    intro u hu
    by_cases hd : q ∣ u
    · exact mem_union_right _ (mem_filter.mpr ⟨hu, hd⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨hu, hd⟩)
  have hbad : bad.card ≤ (N/q-1)/q+1 :=
    IntervalMultiples.card_multiples_interval_le _ _ _
  have hcard := card_le_card hcover
  rw [PrimeRunStarts.parameters_card] at hcard
  have hunion := card_union_le (retainedParameters N q) bad
  omega

theorem starts_card (N q : ℕ) (hq : 0<q) :
    (starts N q).card=(retainedParameters N q).card := by
  apply card_image_of_injective
  intro u v huv
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel huv)

theorem starts_card_lower {N q : ℕ} (hq : 2 ≤ q) (hqN : q ≤ N) :
    (N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3 ≤ (starts N q).card := by
  have hqpos : 0<q := by omega
  have hqR : (0 : ℝ)<q := by exact_mod_cast hqpos
  have hdiv : 1 ≤ N/q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
  have hfloorUpper : ((N/q : ℕ) : ℝ) ≤ (N : ℝ)/q := Nat.cast_div_le
  have hfloorLower : (N : ℝ)/q-1 ≤ (N/q : ℕ) := by
    have hmod := Nat.mod_add_div N q
    have hmodlt := Nat.mod_lt N hqpos
    have hidR : ((N%q : ℕ) : ℝ)+(q : ℝ)*((N/q : ℕ) : ℝ)=N := by exact_mod_cast hmod
    have hltR : ((N%q : ℕ) : ℝ)<q := by exact_mod_cast hmodlt
    have hnext : (N : ℝ)/q ≤ ((N/q : ℕ) : ℝ)+1 := (div_le_iff₀ hqR).mpr (by nlinarith)
    linarith
  have hlength : ((N/q-1 : ℕ) : ℝ)=((N/q : ℕ) : ℝ)-1 := by
    rw [Nat.cast_sub hdiv]
    norm_num
  have hlengthUpper : ((N/q-1 : ℕ) : ℝ) ≤ (N : ℝ)/q := by rw [hlength]; linarith
  have hbadFloor : (((N/q-1)/q : ℕ) : ℝ) ≤ (N : ℝ)/(q : ℝ)^2 := by
    calc
      _ ≤ ((N/q-1 : ℕ) : ℝ)/q := Nat.cast_div_le
      _ ≤ ((N : ℝ)/q)/q := div_le_div_of_nonneg_right hlengthUpper hqR.le
      _ = _ := by ring
  have hcardNat := retainedParameters_card_lower N q
  have hcardR : ((N/q-1 : ℕ) : ℝ) ≤ ((retainedParameters N q).card : ℝ)+
      ((((N/q-1)/q : ℕ) : ℝ)+1) := by exact_mod_cast hcardNat
  rw [starts_card N q hqpos, hlength] at *
  linarith

theorem finite_lower_bound_strictly_improves (N q : ℕ) :
    (N : ℝ)/q-2*(N : ℝ)/(q : ℝ)^2-4 < (N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3 := by
  have h : 0 ≤ (N : ℝ)/(q : ℝ)^2 := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  rw [mul_div_assoc]
  linarith

theorem positive_count_on_sample {M N : ℕ} (q : PrimeUpTo M) (hqN : q.val.val ≤ N) :
    (starts N q.val.val).card ≤
      indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q.val.val-1))
        (OneNegativePrime.sample q) := by
  rw [← card_activeSites]
  apply card_le_card
  intro x hx
  have hbox := starts_subset_interval q.property.two_le hqN hx
  obtain ⟨u, _hu, hu, hxu⟩ := (mem_starts N q.val.val x).mp hx
  have hpattern := positive_start q u hu
  apply mem_filter.mpr
  refine ⟨hbox, ?_⟩
  rw [← hxu]
  simp only [PositiveStarts.indicator, Bool.and_eq_true, decide_eq_true_eq, startIndicator_eq_true_iff]
  exact hpattern

theorem positive_exponential_card_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t*((starts N q).card : ℝ)-(primeCount (dyadicCutoff N (q-1)) : ℝ)*Real.log 2) ≤
      PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  let M := dyadicCutoff N (q-1)
  let p : PrimeUpTo M := ⟨⟨q, by dsimp [M, dyadicCutoff]; omega⟩, hq⟩
  let σ := OneNegativePrime.sample p
  have hcount := positive_count_on_sample p hqN
  have hcountR : ((starts N q).card : ℝ) ≤
      (indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ) := by
    exact_mod_cast hcount
  have hatom := PrimeRunCylinder.finiteExpectation_ge_atom (cylinderProbability M)
    (fun σ ↦ Real.exp (t*(indicatorCount (dyadicBlock N)
      (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ))) (fun _ ↦ (Real.exp_pos _).le) σ
  rw [PositiveStarts.exponentialMoment_eq_finite (subset_refl _)]
  calc
    _ = (cylinderProbability M).weight σ*Real.exp (t*((starts N q).card : ℝ)) := by
      rw [PrimeCylinderSize.atom_weight, Real.exp_sub, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ)<2)]
      ring
    _ ≤ (cylinderProbability M).weight σ*Real.exp
        (t*(indicatorCount (dyadicBlock N) (fun x ↦ PositiveStarts.indicator x (q-1)) σ : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcountR ht))
        ((cylinderProbability M).weight_nonneg σ)
    _ ≤ _ := hatom

theorem positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (dyadicCutoff N (q-1)) : ℝ)*Real.log 2) ≤
        PositiveStarts.exponentialMoment (dyadicBlock N) (q-1) t := by
  exact (Real.exp_le_exp.mpr (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (starts_card_lower hq.two_le hqN) ht) _)).trans
      (positive_exponential_card_lower hq hqN t ht)

theorem total_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q ≤ N)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t*((N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3)-
      (primeCount (dyadicCutoff N (q-1)) : ℝ)*Real.log 2) ≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_lower hq hqN t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

end PaperP1.OneSidedPrimeCylinder
