module

public import PaperP1.Arithmetic.FiniteResidualRank
public import PaperP1.Arithmetic.PrivateWindowPrimes
public import PaperP1.Coding.LocalDefectBound

/-! # At most two large-prime rows on a true subset of two dilated intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoProgressionPrimeRows

open Finset PaperP1.Arithmetic PaperP1.PrimeRowComponents

def progression (a U R : ℕ) : Finset ℕ := (Icc U (U + R)).image (fun n ↦ a * n)

def oddValues (a U R p : ℕ) : Finset ℕ := (progression a U R).filter fun n ↦ parityVec n p ≠ 0

theorem dvd_of_nonzero_parity {n p : ℕ} (hn : parityVec n p ≠ 0) : p ∣ n := by
  by_contra h
  apply hn
  simp only [parityVec_apply, Nat.factorization_eq_zero_of_not_dvd h, Nat.cast_zero]

theorem unique_interval_multiples {u v U R p : ℕ} (hu : u ∈ Icc U (U + R)) (hv : v ∈ Icc U (U + R))
    (hpu : p ∣ u) (hpv : p ∣ v) (hpR : R < p) : u = v := by
  by_contra hne
  have hdist : Nat.dist u v ≤ R := by
    obtain ⟨hu0, hu1⟩ := mem_Icc.mp hu
    obtain ⟨hv0, hv1⟩ := mem_Icc.mp hv
    rw [Nat.dist]
    omega
  have hpdist : p ∣ Nat.dist u v := by
    rcases le_total u v with h | h
    · simpa only [Nat.dist_eq_sub_of_le h] using Nat.dvd_sub hpv hpu
    · simpa only [Nat.dist_eq_sub_of_le_right h] using Nat.dvd_sub hpu hpv
  have hbound := Nat.le_of_dvd (Nat.dist_pos_of_ne hne) hpdist
  omega

theorem oddValues_card_le_one {a U R p : ℕ} (hp : p.Prime) (hpa : ¬p ∣ a) (hpR : R < p) :
    (oddValues a U R p).card ≤ 1 := by
  apply card_le_one.mpr
  intro n hn m hm
  obtain ⟨hnmem, hnpar⟩ := mem_filter.mp hn
  obtain ⟨hmmem, hmpar⟩ := mem_filter.mp hm
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hnmem
  obtain ⟨v, hv, rfl⟩ := mem_image.mp hmmem
  have hpu : p ∣ u := (hp.dvd_mul.mp (dvd_of_nonzero_parity hnpar)).resolve_left hpa
  have hpv : p ∣ v := (hp.dvd_mul.mp (dvd_of_nonzero_parity hmpar)).resolve_left hpa
  exact congrArg (fun u ↦ a * u) (unique_interval_multiples hu hv hpu hpv hpR)

theorem rows_le_two {S P : Finset ℕ} {a b Ux Uy Rx Ry : ℕ}
    (hS : S ⊆ progression a Ux Rx ∪ progression b Uy Ry)
    (hcut : ∀ p, p ∉ P → p.Prime → Rx < p ∧ Ry < p ∧ ¬p ∣ a ∧ ¬p ∣ b) :
    ∀ p, (rows S P p).card ≤ 2 := by
  intro p
  by_cases hpP : p ∈ P
  · simp only [rows, ite_eq_left hpP, card_empty, Nat.zero_le]
  · by_cases hp : p.Prime
    · obtain ⟨hpRx, hpRy, hpa, hpb⟩ := hcut p hpP hp
      have himage : (rows S P p).image Subtype.val ⊆ oddValues a Ux Rx p ∪ oddValues b Uy Ry p := by
        intro n hn
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
        have hpar : parityVec v.val p ≠ 0 := by
          simpa only [rows, ite_eq_right hpP, mem_filter, mem_univ, true_and] using hv
        rcases mem_union.mp (hS v.property) with hn | hn
        · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hn, hpar⟩))
        · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn, hpar⟩))
      have hcard := card_le_card himage
      rw [card_image_of_injective _ Subtype.val_injective] at hcard
      have hunion := card_union_le (oddValues a Ux Rx p) (oddValues b Uy Ry p)
      have hleft := oddValues_card_le_one (U := Ux) hp hpa hpRx
      have hright := oddValues_card_le_one (U := Uy) hp hpb hpRy
      omega
    · have hempty : rows S P p = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro v hv
        have hpar : parityVec v.val p ≠ 0 := by
          simpa only [rows, ite_eq_right hpP, mem_filter, mem_univ, true_and] using hv
        exact hp (DefectParitySupport.prime_of_parityVec_ne_zero hpar)
      rw [hempty, card_empty]
      omega

def exceptionalPrimes (H a b : ℕ) : Finset ℕ :=
  DefectCounting.smallPrimesUpTo H ∪ (a * b).primeFactors

theorem exceptional_covers {H a b : ℕ} (ha : 0 < a) (hb : 0 < b) (p : ℕ)
    (hpP : p ∉ exceptionalPrimes H a b) (hp : p.Prime) : H < p ∧ ¬p ∣ a ∧ ¬p ∣ b := by
  have hsmall : p ∉ DefectCounting.smallPrimesUpTo H := fun h ↦ hpP (mem_union.mpr (Or.inl h))
  have hproduct : ¬p ∣ a * b := by
    intro hdiv
    exact hpP (mem_union.mpr (Or.inr (Nat.mem_primeFactors.mpr ⟨hp, hdiv, (Nat.mul_pos ha hb).ne'⟩)))
  refine ⟨?_, fun h ↦ hproduct (dvd_mul_of_dvd_left h b), fun h ↦ hproduct (dvd_mul_of_dvd_right h a)⟩
  by_contra h
  exact hsmall (DefectCounting.mem_smallPrimesUpTo.mpr ⟨hp, by omega⟩)

theorem rows_le_two_actual_cutoff {S : Finset ℕ} {H a b Ux Uy Rx Ry : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hRx : Rx ≤ H) (hRy : Ry ≤ H)
    (hS : S ⊆ progression a Ux Rx ∪ progression b Uy Ry) :
    ∀ p, (rows S (exceptionalPrimes H a b) p).card ≤ 2 := by
  apply rows_le_two hS
  intro p hpP hp
  obtain ⟨hHp, hpa, hpb⟩ := exceptional_covers ha hb p hpP hp
  exact ⟨hRx.trans_lt hHp, hRy.trans_lt hHp, hpa, hpb⟩

theorem exceptional_card (H a b : ℕ) :
    (exceptionalPrimes H a b).card ≤ LocalDefectBound.primeCount H + (a * b).primeFactors.card :=
  card_union_le _ _

end PaperP1.TwoProgressionPrimeRows
