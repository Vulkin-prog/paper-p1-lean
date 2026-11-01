module

public import PaperP1.Arithmetic.ChannelPlacements
public import PaperP1.Arithmetic.ActualSourceTranslations
public import PaperP1.Arithmetic.WeightedTranslationError

/-! # Actual translation sums over finite channel words and their signed main terms -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelWordHosts

open Finset PaperP1.ChannelPlacements PaperP1.ChannelSumIdentity PaperP1.ActualSourceTranslations

def Patterns (L a b : ℕ) :=
  Σ d : ↥(Icc 1 (L / b)), ↥(placements L (a * d.val)) × ↥(placements L (b * d.val))

instance patternsFintype (L a b : ℕ) : Fintype (Patterns L a b) := by
  unfold Patterns
  infer_instance

def patternWeight {L a b : ℕ} (p : Patterns L a b) : ℚ := (weight p.1.val : ℤ)

def patternSign {L a b : ℕ} (p : Patterns L a b) : ℚ :=
  (placementSign p.2.1.val : ℤ) * (placementSign p.2.2.val : ℤ)

def placementIndex (L i : ℕ) : Fin (L + 1) := ⟨i % (L + 1), Nat.mod_lt _ (by omega)⟩

def sourceCount (N : ℕ) {L a b : ℕ} (p : Patterns L a b) : ℚ :=
  (symmetricSources N a b L (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).card

def unsignedHosts (N L a b : ℕ) : ℚ := ∑ p : Patterns L a b, patternWeight p * sourceCount N p

def signedHosts (N L a b : ℕ) : ℚ :=
  ∑ p : Patterns L a b, patternWeight p * patternSign p * sourceCount N p

theorem placement_index_val {L D : ℕ} (i : ↥(placements L D)) :
    (placementIndex L i.val).val = i.val := by
  apply Nat.mod_eq_of_lt
  have hi := i.property
  unfold placements at hi
  split at hi
  · exact (mem_range.mp hi).trans_le (Nat.sub_le _ _)
  · simp at hi

theorem weight_nonneg (d : ℕ) : (0 : ℚ) ≤ (weight d : ℤ) := by
  have h : (0 : ℤ) ≤ weight d := by unfold weight; split <;> positivity
  exact_mod_cast h

theorem sign_abs (i : ℕ) : |(placementSign i : ℚ)| = 1 := by
  unfold placementSign
  split <;> norm_num

theorem pattern_sign_abs {L a b : ℕ} (p : Patterns L a b) : |patternSign p| = 1 := by
  unfold patternSign
  rw [abs_mul, sign_abs, sign_abs, one_mul]

theorem pattern_sum (L a b : ℕ) (f : ℕ → ℕ → ℕ → ℚ) :
    (∑ p : Patterns L a b, f p.1.val p.2.1.val p.2.2.val) =
      ∑ d ∈ Icc 1 (L / b), ∑ i ∈ placements L (a * d), ∑ j ∈ placements L (b * d), f d i j := by
  change (∑ p : (Σ d : ↥(Icc 1 (L / b)), ↥(placements L (a * d.val)) × ↥(placements L (b * d.val))),
    f p.1.val p.2.1.val p.2.2.val) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ d : ↥(Icc 1 (L / b)), ∑ i ∈ placements L (a * d.val),
        ∑ j ∈ placements L (b * d.val), f d.val i j := by
      apply sum_congr rfl
      intro d _
      calc
        _ = ∑ i : ↥(placements L (a * d.val)), ∑ j ∈ placements L (b * d.val), f d.val i.val j := by
          apply sum_congr rfl
          intro i _
          exact sum_coe_sort (placements L (b * d.val)) (fun j ↦ f d.val i.val j)
        _ = _ := sum_coe_sort (placements L (a * d.val))
          (fun i ↦ ∑ j ∈ placements L (b * d.val), f d.val i j)
    _ = _ := sum_coe_sort (Icc 1 (L / b))
      (fun d ↦ ∑ i ∈ placements L (a * d), ∑ j ∈ placements L (b * d), f d i j)

theorem unsigned_weight_sum (L a b : ℕ) :
    (∑ p : Patterns L a b, patternWeight p) = (unsignedPairSum L a b : ℤ) := by
  change (∑ p : Patterns L a b,
    ((weight p.1.val : ℤ) : ℚ)) = _
  rw [pattern_sum L a b (fun d _ _ ↦ (weight d : ℚ))]
  simp only [sum_const, nsmul_eq_mul]
  simp only [unsignedPairSum, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply sum_congr rfl
  intro d _
  ring

theorem signed_weight_sum (L a b : ℕ) :
    (∑ p : Patterns L a b, patternWeight p * patternSign p) = (signedPairSum L a b : ℤ) := by
  change (∑ p : Patterns L a b,
    ((weight p.1.val : ℤ) : ℚ) * ((placementSign p.2.1.val : ℤ) * (placementSign p.2.2.val : ℤ))) = _
  rw [pattern_sum L a b (fun d i j ↦ (weight d : ℚ) * ((placementSign i : ℚ) * (placementSign j : ℚ)))]
  simp only [signedPairSum, signedPlacements, Int.cast_sum, Int.cast_mul]
  apply sum_congr rfl
  intro d _
  rw [mul_assoc, sum_mul_sum]
  simp_rw [mul_sum]

theorem unsigned_weight_total {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    (∑ p : Patterns L a b, patternWeight p) = (unsigned L a b : ℤ) := by
  rw [unsigned_weight_sum, unsigned_pair_sum_eq hb hab]

theorem signed_weight_total {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    (∑ p : Patterns L a b, patternWeight p * patternSign p) = (signed L a b : ℤ) := by
  rw [signed_weight_sum, signed_pair_sum_eq hb hab]

theorem unsigned_nonneg {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) : (0 : ℤ) ≤ unsigned L a b := by
  have h : (0 : ℚ) ≤ (unsigned L a b : ℤ) := by
    rw [← unsigned_weight_total hb hab]
    exact sum_nonneg (fun p _ ↦ weight_nonneg p.1.val)
  exact_mod_cast h

theorem signed_abs_le_unsigned {L a b : ℕ} (hb : 0 < b) (hab : a ≤ b) :
    |signed L a b| ≤ unsigned L a b := by
  have h : |((signed L a b : ℤ) : ℚ)| ≤ ((unsigned L a b : ℤ) : ℚ) := by
    rw [← signed_weight_total hb hab, ← unsigned_weight_total hb hab]
    calc
      _ ≤ ∑ p : Patterns L a b, |patternWeight p * patternSign p| := abs_sum_le_sum_abs _ _
      _ = _ := by
        apply sum_congr rfl
        intro p _
        have hw : 0 ≤ patternWeight p := weight_nonneg p.1.val
        rw [abs_mul, abs_of_nonneg hw, pattern_sign_abs, mul_one]
  exact_mod_cast h

theorem unsigned_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    |unsignedHosts N L a b - (N : ℚ) * coefficient a b * (unsigned L a b : ℤ)| ≤
      6 * ((L + 1 : ℕ) : ℚ) * (unsigned L a b : ℤ) := by
  have h := WeightedTranslationError.weighted_error (univ : Finset (Patterns L a b))
    patternWeight (fun _ ↦ 1) (sourceCount N) ((N : ℚ) * coefficient a b) (6 * ((L + 1 : ℕ) : ℚ))
    (fun p _ ↦ weight_nonneg p.1.val) (fun _ _ ↦ by norm_num)
    (fun p _ ↦ (simple_errors hN ha hab hinterior hcop hlarge
      (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).2)
  simp only [mul_one] at h
  rw [unsigned_weight_total (ha.trans hab) hab.le] at h
  exact h

theorem signed_error {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    |signedHosts N L a b - (N : ℚ) * coefficient a b * (signed L a b : ℤ)| ≤
      6 * ((L + 1 : ℕ) : ℚ) * (unsigned L a b : ℤ) := by
  have h := WeightedTranslationError.weighted_error (univ : Finset (Patterns L a b))
    patternWeight patternSign (sourceCount N) ((N : ℚ) * coefficient a b) (6 * ((L + 1 : ℕ) : ℚ))
    (fun p _ ↦ weight_nonneg p.1.val) (fun p _ ↦ (pattern_sign_abs p).le)
    (fun p _ ↦ (simple_errors hN ha hab hinterior hcop hlarge
      (placementIndex L p.2.1.val) (placementIndex L p.2.2.val)).2)
  rw [signed_weight_total (ha.trans hab) hab.le, unsigned_weight_total (ha.trans hab) hab.le] at h
  exact h

end PaperP1.ChannelWordHosts
