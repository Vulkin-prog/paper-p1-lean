module

public import PaperP1.Model.ValuationPrimeCylinder

/-! # Effective finite bounds from the even valuation layers
The actual retained starts have count at least
N/(q+1)*(1-(1/q)^(2*k))-3*k for every finite depth k.
The same supported cylinder bounds both full exponential moments.
A proved critical-scale example makes depth two strictly stronger than
one; the error term means that increasing depth need not improve the
explicit budget in general. No new asymptotic threshold is asserted.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.ValuationLayerCounts

open Finset PaperP1.Arithmetic

def multiples (U B d : ℕ) : Finset ℕ := (Ico U (U+B)).filter fun u ↦ d∣u

def layer (U B q j : ℕ) : Finset ℕ :=
  (Ico U (U+B)).filter fun u ↦ q^(2*j)∣u ∧ ¬q^(2*j+1)∣u

def coefficient (q j : ℕ) : ℝ := (1/(q : ℝ))^(2*j)-(1/(q : ℝ))^(2*j+1)

def parameterLayer (N q j : ℕ) : Finset ℕ := layer (N/q+1) (N/q-1) q j

def budget (N q k : ℕ) : ℝ :=
  (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k))-3*(k : ℝ)

theorem card_positive_multiples (X d : ℕ) :
    ((Icc 1 X).filter fun u ↦ d∣u).card=X/d := by
  have heq : ((Icc 1 X).filter fun u ↦ d∣u)=
      (range (X+1)).filter (fun u ↦ u≠0 ∧ d∣u) := by
    ext u
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [heq]
  exact Nat.card_multiples' X d

theorem translated_multiples_eq_sdiff (U B d : ℕ) (hU : 1≤U) :
    ((Ico U (U+B)).filter fun u ↦ d∣u)=
      ((Icc 1 (U+B-1)).filter fun u ↦ d∣u)\
        ((Icc 1 (U-1)).filter fun u ↦ d∣u) := by
  ext u
  simp only [mem_filter,mem_sdiff,mem_Icc,mem_Ico]
  omega

theorem card_translated_multiples (U B d : ℕ) (hU : 1≤U) :
    ((Ico U (U+B)).filter fun u ↦ d∣u).card=(U+B-1)/d-(U-1)/d := by
  rw [translated_multiples_eq_sdiff U B d hU,card_sdiff_of_subset]
  · rw [card_positive_multiples,card_positive_multiples]
  · intro u hu
    obtain ⟨hu,hdiv⟩ := mem_filter.mp hu
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hu).1,by have h := (mem_Icc.mp hu).2; omega⟩,hdiv⟩

theorem real_div_floor_lower (x d : ℕ) (hd : 0<d) :
    (x : ℝ)/d-1≤((x/d : ℕ) : ℝ) := by
  have hdR : (0 : ℝ)<d := by exact_mod_cast hd
  have hmod := Nat.mod_add_div x d
  have hmodlt := Nat.mod_lt x hd
  have hidR : ((x%d : ℕ) : ℝ)+(d : ℝ)*((x/d : ℕ) : ℝ)=x := by exact_mod_cast hmod
  have hltR : ((x%d : ℕ) : ℝ)<d := by exact_mod_cast hmodlt
  have hnext : (x : ℝ)/d≤((x/d : ℕ) : ℝ)+1 := (div_le_iff₀ hdR).mpr (by nlinarith)
  linarith

theorem card_translated_multiples_real_bounds (U B d : ℕ) (hU : 1≤U) (hd : 0<d) :
    (B : ℝ)/d-1≤(((Ico U (U+B)).filter fun u ↦ d∣u).card : ℝ) ∧
    (((Ico U (U+B)).filter fun u ↦ d∣u).card : ℝ)≤(B : ℝ)/d+1 := by
  have hsub : (U-1)/d≤(U+B-1)/d := Nat.div_le_div_right (by omega)
  rw [card_translated_multiples U B d hU,Nat.cast_sub hsub]
  have hlowA := real_div_floor_lower (U+B-1) d hd
  have hlowB := real_div_floor_lower (U-1) d hd
  have hupA : (((U+B-1)/d : ℕ) : ℝ)≤((U+B-1 : ℕ) : ℝ)/d := Nat.cast_div_le
  have hupB : (((U-1)/d : ℕ) : ℝ)≤((U-1 : ℕ) : ℝ)/d := Nat.cast_div_le
  have hcastA : ((U+B-1 : ℕ) : ℝ)=(U : ℝ)+B-1 := by
    rw [Nat.cast_sub (by omega : 1≤U+B),Nat.cast_add,Nat.cast_one]
  have hcastB : ((U-1 : ℕ) : ℝ)=(U : ℝ)-1 := by rw [Nat.cast_sub hU,Nat.cast_one]
  rw [hcastA] at hlowA hupA
  rw [hcastB] at hlowB hupB
  have heq : ((U : ℝ)+B-1)/d-((U : ℝ)-1)/d=(B : ℝ)/d := by ring
  constructor <;> linarith

theorem next_power_multiples_subset (U B q j : ℕ) :
    multiples U B (q^(2*j+1))⊆multiples U B (q^(2*j)) := by
  intro u hu
  obtain ⟨hu,hdiv⟩ := mem_filter.mp hu
  apply mem_filter.mpr
  refine ⟨hu,?_⟩
  have hpower : q^(2*j)∣q^(2*j+1) := by rw [pow_succ]; exact dvd_mul_right _ _
  exact hpower.trans hdiv

theorem layer_eq_sdiff (U B q j : ℕ) :
    layer U B q j=multiples U B (q^(2*j))\multiples U B (q^(2*j+1)) := by
  ext u
  simp only [layer,multiples,mem_filter,mem_sdiff]
  tauto

theorem card_layer (U B q j : ℕ) :
    (layer U B q j).card=(multiples U B (q^(2*j))).card-
      (multiples U B (q^(2*j+1))).card := by
  rw [layer_eq_sdiff,card_sdiff_of_subset (next_power_multiples_subset U B q j)]

theorem layer_parity_zero {U B q j u : ℕ} (hq : 0<q) (hu : u∈layer U B q j) :
    parityVec u q=0 := by
  obtain ⟨_hu,hdiv,hnot⟩ := mem_filter.mp hu
  obtain ⟨v,rfl⟩ := hdiv
  have hvnot : ¬q∣v := by
    intro hqv
    apply hnot
    rw [pow_succ]
    exact Nat.mul_dvd_mul_left _ hqv
  have hvne : v≠0 := by intro h;exact hvnot (h ▸ dvd_zero q)
  have hpowne : q^(2*j)≠0 := (pow_pos hq _).ne'
  have hparity : parityVec (q^(2*j))=0 := by
    have heq : 2*j=j*2 := by omega
    rw [heq,pow_mul,parityVec_pow_two]
  rw [parityVec_mul hpowne hvne,Finsupp.add_apply,hparity,Finsupp.zero_apply,
    OneNegativePrime.parity_zero_of_not_dvd hvnot,add_zero]

theorem card_layer_real_lower (U B q j : ℕ) (hU : 1≤U) (hq : 0<q) :
    (B : ℝ)*coefficient q j-2≤((layer U B q j).card : ℝ) := by
  have ha := (card_translated_multiples_real_bounds U B (q^(2*j)) hU (pow_pos hq _)).1
  have hb := (card_translated_multiples_real_bounds U B (q^(2*j+1)) hU (pow_pos hq _)).2
  have hcard := card_le_card (next_power_multiples_subset U B q j)
  rw [card_layer,Nat.cast_sub hcard]
  change (B : ℝ)*coefficient q j-2≤
    (((Ico U (U+B)).filter fun u ↦ q^(2*j)∣u).card : ℝ)-
      (((Ico U (U+B)).filter fun u ↦ q^(2*j+1)∣u).card : ℝ)
  simp only [Nat.cast_pow] at ha hb
  have heq : (B : ℝ)*coefficient q j=
      (B : ℝ)/(q : ℝ)^(2*j)-(B : ℝ)/(q : ℝ)^(2*j+1) := by
    simp only [coefficient,one_div_pow]
    ring
  rw [heq]
  linarith

theorem coefficient_nonneg {q : ℕ} (hq : 1≤q) (j : ℕ) : 0≤coefficient q j := by
  let r : ℝ := 1/(q : ℝ)
  have hqR : (1 : ℝ)≤q := by exact_mod_cast hq
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hr1 : r≤1 := by
    dsimp [r]
    exact (div_le_one (by linarith : (0 : ℝ)<q)).mpr hqR
  have hprod := mul_nonneg (pow_nonneg hr0 (2*j)) (sub_nonneg.mpr hr1)
  change 0≤r^(2*j)-r^(2*j+1)
  rw [pow_succ]
  nlinarith

theorem coefficient_le_half {q j : ℕ} (hq : 2≤q) (hj : 1≤j) :
    coefficient q j≤1/2 := by
  let r : ℝ := 1/(q : ℝ)
  have hqR : (2 : ℝ)≤q := by exact_mod_cast hq
  have hr0 : 0≤r := by dsimp [r]; positivity
  have hrhalf : r≤1/2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<2) hqR
  have hr1 : r≤1 := by linarith
  have hprev : r^(2*j-1)≤1 := pow_le_one₀ hr0 hr1
  have hprod := mul_nonneg hr0 (sub_nonneg.mpr hprev)
  have hpow : r^(2*j)≤r := by
    rw [show 2*j=(2*j-1)+1 by omega,pow_succ]
    nlinarith
  have hnext := pow_nonneg hr0 (2*j+1)
  change r^(2*j)-r^(2*j+1)≤1/2
  linarith

theorem coefficient_telescopes (q j : ℕ) (hq : 0<q) :
    coefficient q j=(q : ℝ)/((q : ℝ)+1)*
      ((1/(q : ℝ))^(2*j)-(1/(q : ℝ))^(2*(j+1))) := by
  let r : ℝ := 1/(q : ℝ)
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hqplus : (q : ℝ)+1≠0 := by positivity
  have hbase : 1-r=(q : ℝ)/((q : ℝ)+1)*(1-r^2) := by
    dsimp [r]
    field_simp
    ring
  have hstep1 : r^(2*j+1)=r^(2*j)*r := pow_succ _ _
  have hstep2 : r^(2*(j+1))=r^(2*j)*r^2 := by
    rw [show 2*(j+1)=2*j+2 by omega,pow_add]
  change r^(2*j)-r^(2*j+1)=(q : ℝ)/((q : ℝ)+1)*(r^(2*j)-r^(2*(j+1)))
  rw [hstep1,hstep2]
  calc
    _ = r^(2*j)*(1-r) := by ring
    _ = r^(2*j)*((q : ℝ)/((q : ℝ)+1)*(1-r^2)) := by rw [hbase]
    _ = _ := by ring

theorem sum_coefficients (q k : ℕ) (hq : 0<q) :
    (∑ j ∈ range k,coefficient q j)=
      (q : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ,ih,coefficient_telescopes q k hq]
    ring

theorem layers_disjoint (U B q : ℕ) {i j : ℕ} (hij : i≠j) :
    Disjoint (layer U B q i) (layer U B q j) := by
  apply disjoint_left.mpr
  intro u hui huj
  obtain ⟨_hui,hdivi,hnoti⟩ := mem_filter.mp hui
  obtain ⟨_huj,hdivj,hnotj⟩ := mem_filter.mp huj
  obtain hij | hji := lt_or_gt_of_ne hij
  · exact hnoti ((pow_dvd_pow q (by omega : 2*i+1≤2*j)).trans hdivj)
  · exact hnotj ((pow_dvd_pow q (by omega : 2*j+1≤2*i)).trans hdivi)

theorem parameterLayer_subset {N q j : ℕ} (hq : 0<q) :
    parameterLayer N q j⊆ValuationPrimeCylinder.retainedParameters N q := by
  intro u hu
  apply mem_filter.mpr
  exact ⟨(mem_filter.mp hu).1,layer_parity_zero hq hu⟩

theorem sum_layer_card_le (N q k : ℕ) (hq : 0<q) :
    (∑ j ∈ range k,(parameterLayer N q j).card)≤
      (ValuationPrimeCylinder.retainedParameters N q).card := by
  let F := (range k).biUnion (parameterLayer N q)
  have hpair : (↑(range k) : Set ℕ).PairwiseDisjoint (parameterLayer N q) := by
    intro i _hi j _hj hij
    exact layers_disjoint _ _ _ hij
  have hcard : F.card=∑ j ∈ range k,(parameterLayer N q j).card := card_biUnion hpair
  have hsub : F⊆ValuationPrimeCylinder.retainedParameters N q := by
    intro u hu
    obtain ⟨j,_hj,hu⟩ := mem_biUnion.mp hu
    exact parameterLayer_subset hq hu
  rw [← hcard]
  exact card_le_card hsub

theorem valuation_starts_card (N q : ℕ) (hq : 0<q) :
    (ValuationPrimeCylinder.starts N q).card=(ValuationPrimeCylinder.retainedParameters N q).card := by
  apply card_image_of_injective
  intro u v huv
  exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel huv)

theorem parameterLayer_zero (N q : ℕ) : parameterLayer N q 0=OneSidedPrimeCylinder.retainedParameters N q := by
  ext u
  simp only [parameterLayer,layer,OneSidedPrimeCylinder.retainedParameters,PrimeRunStarts.parameters,
    mem_filter,Nat.mul_zero,Nat.zero_add,pow_zero,pow_one,one_dvd,true_and]

theorem parameter_layer_real_lower {N q : ℕ} (hq : 2≤q) (hqN : q≤N) (j : ℕ) :
    (N : ℝ)/q*coefficient q j-3≤((parameterLayer N q j).card : ℝ) := by
  have hqpos : 0<q := by omega
  by_cases hj : j=0
  · subst j
    rw [parameterLayer_zero]
    have hbase := OneSidedPrimeCylinder.starts_card_lower hq hqN
    rw [OneSidedPrimeCylinder.starts_card N q hqpos] at hbase
    have heq : (N : ℝ)/q*coefficient q 0-3=
        (N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3 := by
      simp only [coefficient,Nat.mul_zero,Nat.zero_add,pow_zero,pow_one]
      have hqne : (q : ℝ)≠0 := by exact_mod_cast hqpos.ne'
      field_simp
    rw [heq]
    exact hbase
  · have hjpos : 1≤j := by omega
    have hdiv : 1≤N/q := (Nat.le_div_iff_mul_le hqpos).mpr (by simpa only [one_mul] using hqN)
    have hlen : (N : ℝ)/q-2≤((N/q-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hdiv,Nat.cast_one]
      have hfloor := real_div_floor_lower N q hqpos
      linarith
    have hc0 := coefficient_nonneg (by omega : 1≤q) j
    have hc1 := coefficient_le_half hq hjpos
    have hcard := card_layer_real_lower (N/q+1) (N/q-1) q j (by omega) hqpos
    have hmul := mul_le_mul_of_nonneg_right hlen hc0
    change (N : ℝ)/q*coefficient q j-3≤((layer (N/q+1) (N/q-1) q j).card : ℝ)
    nlinarith

theorem partial_layers_real_lower {N q : ℕ} (hq : 2≤q) (hqN : q≤N) (k : ℕ) :
    (N : ℝ)/q*(∑ j ∈ range k,coefficient q j)-3*(k : ℝ)≤
      ((ValuationPrimeCylinder.starts N q).card : ℝ) := by
  have hqpos : 0<q := by omega
  have hsum := sum_le_sum (fun j (_hj : j∈range k) ↦ parameter_layer_real_lower hq hqN j)
  have hcard : (∑ j ∈ range k,((parameterLayer N q j).card : ℝ))≤
      ((ValuationPrimeCylinder.retainedParameters N q).card : ℝ) := by
    exact_mod_cast sum_layer_card_le N q k hqpos
  have heq : (∑ j ∈ range k,((N : ℝ)/q*coefficient q j-3))=
      (N : ℝ)/q*(∑ j ∈ range k,coefficient q j)-3*(k : ℝ) := by
    rw [sum_sub_distrib]
    simp only [← mul_sum,sum_const,card_range,nsmul_eq_mul]
    ring
  rw [heq] at hsum
  rw [valuation_starts_card N q hqpos]
  exact hsum.trans hcard

theorem finite_geometric_lower {N q : ℕ} (hq : 2≤q) (hqN : q≤N) (k : ℕ) :
    (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k))-3*(k : ℝ)≤
      ((ValuationPrimeCylinder.starts N q).card : ℝ) := by
  have hqpos : 0<q := by omega
  have h := partial_layers_real_lower hq hqN k
  rw [sum_coefficients q k hqpos] at h
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hqpos.ne'
  have heq : (N : ℝ)/q*((q : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k)))=
      (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k)) := by
    calc
      _ = ((N : ℝ)/q*q)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*k)) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hqne]
  rwa [heq] at h

theorem budget_one (N q : ℕ) (hq : 0<q) :
    budget N q 1=(N : ℝ)/q-(N : ℝ)/(q : ℝ)^2-3 := by
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  have hqplus : (q : ℝ)+1≠0 := by positivity
  norm_num only [budget,Nat.cast_one,Nat.mul_one]
  field_simp
  ring

theorem positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    Real.exp (t*budget N q k-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (Model.dyadicBlock N) (q-1) t :=
  (Real.exp_le_exp.mpr (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (finite_geometric_lower hq.two_le hqN k) ht) _)).trans
      (ValuationPrimeCylinder.positive_exponential_card_lower hq hqN t ht)

theorem total_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (k : ℕ) (t : ℝ) (ht : 0≤t) :
    Real.exp (t*budget N q k-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_lower hq hqN k t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem strict_budget_gain_on_original_scale : budget (2^(17-1)) 17 1<budget (2^(17-1)) 17 2 := by
  norm_num [budget]

theorem strict_exponential_gain_on_original_scale (t : ℝ) (ht : 0<t) :
    Real.exp (t*budget (2^(17-1)) 17 1-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff (2^(17-1)) 17) : ℝ)*Real.log 2)<
    Real.exp (t*budget (2^(17-1)) 17 2-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff (2^(17-1)) 17) : ℝ)*Real.log 2) := by
  exact Real.exp_lt_exp.mpr (sub_lt_sub_right
    (mul_lt_mul_of_pos_left strict_budget_gain_on_original_scale ht) _)

end PaperP1.ValuationLayerCounts
