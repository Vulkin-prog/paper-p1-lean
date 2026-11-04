module

public import PaperP1.Arithmetic.CleanPivotTargets
public import PaperP1.Model.AnchoredWindowForcing

/-! # A clean arithmetic pivot target changes exactly its first raw bit

These are pointwise identities for the original multiplicative prime model.
They do not assume source/target independence. The selected prime has
valuation exactly one at the target's first argument, and every other
changed prime is excluded from the complete target support.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivatePivotTargetFlip

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing PaperP1.PrivatePivotGeometry PaperP1.CleanPivotTargets
  PaperP1.AnchoredPrivateValues

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem value_force (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂)
    (ω : SampleSpace M) (n : ℕ) :
    valueBit (forceWord v q b ω) n = valueBit ω n +
      ∑ i, (b i - valueBit ω (v i)) * parityVec n (q i).val.val := by
  change valueLinear M n (ω + liftBlock q (b - valueSystem M v ω)) = _
  rw [map_add]
  simp only [liftBlock, map_sum, map_smul, valueLinear_apply, valueBit_prime_basis,
    Pi.sub_apply, valueSystem_apply, smul_eq_mul]

omit [DecidableEq ι] in
theorem value_force_selected (v : ι → ℕ) (q : ι → PrimeUpTo M) (b : ι → F₂)
    (ω : SampleSpace M) (n : ℕ) (selected : ι)
    (hselected : parityVec n (q selected).val.val = 1)
    (hother : ∀ i, i ≠ selected → parityVec n (q i).val.val = 0) :
    valueBit (forceWord v q b ω) n = valueBit ω n + (b selected - valueBit ω (v selected)) := by
  rw [value_force, Fintype.sum_eq_single selected]
  · rw [hselected, mul_one]
  · intro i hi
    rw [hother i hi, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
theorem parity_one_of_square_excluded {n p : ℕ} (hp : p.Prime) (hdiv : p ∣ n)
    (hsq : ¬p ^ 2 ∣ n) : parityVec n p = 1 := by
  have hn : n ≠ 0 := by
    intro h
    apply hsq
    rw [h]
    exact dvd_zero _
  have hpos := hp.factorization_pos_of_dvd hn hdiv
  have hlt : n.factorization p < 2 := by
    by_contra h
    exact hsq ((hp.pow_dvd_iff_le_factorization hn).mpr (le_of_not_gt h))
  have he : n.factorization p = 1 := by omega
  simp only [parityVec_apply, he, Nat.cast_one]

omit [Fintype ι] [DecidableEq ι] in
theorem not_dvd_other_offset {n p K : ℕ} (hwidth : K + 1 ≤ p) (hdiv : p ∣ n)
    (k : Fin (K + 1)) (hk : k ≠ 0) : ¬p ∣ n + k.val := by
  intro h
  exact hk (private_divisor hwidth k 0 h (by simpa only [Fin.val_zero, Nat.add_zero] using hdiv))

def otherPrimes (q : ι → PrimeUpTo M) (selected : ι) : Finset ℕ :=
  (univ.erase selected).image (fun i ↦ (q i).val.val)

theorem mem_otherPrimes (q : ι → PrimeUpTo M) (selected i : ι) (hi : i ≠ selected) :
    (q i).val.val ∈ otherPrimes q selected :=
  mem_image.mpr ⟨i, mem_erase.mpr ⟨hi, mem_univ _⟩, rfl⟩

theorem otherPrimes_card (q : ι → PrimeUpTo M) (selected : ι) :
    (otherPrimes q selected).card ≤ Fintype.card ι - 1 := by
  calc
    _ ≤ (univ.erase selected : Finset ι).card := card_image_le
    _ = _ := by rw [card_erase_of_mem (mem_univ _), card_univ]

theorem otherPrimes_coprime (q : ι → PrimeUpTo M) (hinj : Function.Injective q)
    (selected : ι) : ∀ r ∈ otherPrimes q selected, (q selected).val.val.Coprime r := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
  apply (Nat.coprime_primes (q selected).property (q i).property).mpr
  intro he
  apply (mem_erase.mp hi).1
  apply hinj
  apply Subtype.ext
  apply Fin.ext
  exact he.symm

theorem otherPrimes_above (q : ι → PrimeUpTo M) (Y : ℕ)
    (chosen : ι) (hY : ∀ i, Y ≤ (q i).val.val) :
    ∀ r ∈ otherPrimes q chosen, Y ≤ r := by
  intro r hr
  obtain ⟨i, _, rfl⟩ := mem_image.mp hr
  exact hY i

theorem target_word_flip {A N n K : ℕ} (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (b : ι → F₂) (ω : SampleSpace M) (selected : ι)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ targets A N (q selected).val.val (K + 1) (otherPrimes q selected)) :
    valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) (forceWord v q b ω) =
      valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω +
        Pi.single 0 (b selected - valueBit ω (v selected)) := by
  obtain ⟨_, hdiv, hsq, hother⟩ := mem_targets.mp hclean
  have hp : parityVec n (q selected).val.val = 1 :=
    parity_one_of_square_excluded (q selected).property hdiv hsq
  funext k
  by_cases hk : k = 0
  · subst k
    simp only [valueSystem_apply, Fin.val_zero, Nat.add_zero, Pi.add_apply, Pi.single_eq_same]
    apply value_force_selected v q b ω n selected hp
    intro i hi
    have hn := hother (q i).val.val (mem_otherPrimes q selected i hi) 0
    simp only [Fin.val_zero, Nat.add_zero] at hn
    simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd hn, Nat.cast_zero]
  · simp only [valueSystem_apply, Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]
    apply forceWord_preserves_value
    intro i
    by_cases hi : i = selected
    · subst i
      exact not_dvd_other_offset hwidth hdiv k hk
    · exact hother (q i).val.val (mem_otherPrimes q selected i hi) k

omit [Fintype ι] [DecidableEq ι] in
theorem anchored_coefficient (x y b c : F₂) : (b - c) - (x - y) = x - (b + (y - c)) := by
  revert x y b c
  decide

theorem anchored_target_word_flip {A N n K : ℕ} (v : ι → ℕ) (anchor : ι)
    (hpos : ∀ i, 0 < v i) (q : Free anchor → PrimeUpTo M) (b : ι → F₂)
    (ω : SampleSpace M) (selected : Free anchor)
    (hwidth : K + 1 ≤ (q selected).val.val)
    (hclean : n ∈ targets A N (q selected).val.val (K + 1) (otherPrimes q selected)) :
    valueSystem M (fun k : Fin (K + 1) ↦ n + k.val)
      (AnchoredPrivateForcing.force v anchor q b ω) =
    valueSystem M (fun k : Fin (K + 1) ↦ n + k.val) ω +
      Pi.single 0 (valueBit ω (v selected.val) - (b selected.val + (valueBit ω (v anchor) - b anchor))) := by
  have h := target_word_flip (relativeValues v anchor) q (relativeWord b anchor) ω selected hwidth hclean
  have hv : valueBit ω (relativeValues v anchor selected) =
      valueBit ω (v selected.val) - valueBit ω (v anchor) :=
    relative_value v anchor hpos ω selected
  simpa only [AnchoredPrivateForcing.force, relativeWord, hv, anchored_coefficient] using h

end PaperP1.PrivatePivotTargetFlip
