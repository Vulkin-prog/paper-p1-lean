module

public import PaperP1.Asymptotics.TernaryGroupScales

/-! # The actual three-group tail above N^(6/5) -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryStrongCritical

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts
  PaperP1.FiniteEvenSquareClasses PaperP1.TernaryGroupScales

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def coefficient (D : ℕ) : ℝ :=
  2 * IntegerProductTail.productConstant 2 * (D : ℝ) ^ 2 * logConstant + 4 * D * (D + 1)

theorem coefficient_nonneg (D : ℕ) : 0 ≤ coefficient D := by
  unfold coefficient
  have hc := (IntegerProductTail.productConstant_pos 2 (by norm_num)).le
  have hl := logConstant_nonneg
  positivity

theorem numeric_bracket (N L D : ℕ) (hN : 2 ≤ N)
    (hlog : Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) ≤ logConstant * ((L + 1 : ℕ) : ℝ)) :
    2 * IntegerProductTail.productConstant 2 * (D * N : ℕ) ^ 2 *
        ((N : ℝ) ^ (4 / 5 : ℝ)) ^ (-1 : ℝ) * Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) +
      2 * (2 * (D * N) * (D * (L + 1) + 1) : ℕ) * (N : ℝ) ^ (1 / 10 : ℝ) ≤
        coefficient D * ((L + 1 : ℕ) : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hb : (1 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ L + 1)
  have hc := (IntegerProductTail.productConstant_pos 2 (by norm_num)).le
  have hpow : (N : ℝ) ^ 2 * ((N : ℝ) ^ (4 / 5 : ℝ)) ^ (-1 : ℝ) = (N : ℝ) ^ (6 / 5 : ℝ) := by
    rw [← Real.rpow_mul hn.le, ← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_add hn]
    congr 1
    norm_num
  have hsmall : (N : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) := by
    calc
      _ = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) := by rw [Real.rpow_one]
      _ = (N : ℝ) ^ (11 / 10 : ℝ) := by rw [← Real.rpow_add hn]; congr 1; norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hfirst : 2 * IntegerProductTail.productConstant 2 * (D * N : ℕ) ^ 2 *
      ((N : ℝ) ^ (4 / 5 : ℝ)) ^ (-1 : ℝ) * Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) ≤
      (2 * IntegerProductTail.productConstant 2 * (D : ℝ) ^ 2 * logConstant) *
        ((L + 1 : ℕ) : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ) := by
    calc
      _ = (2 * IntegerProductTail.productConstant 2 * (D : ℝ) ^ 2) *
          ((N : ℝ) ^ 2 * ((N : ℝ) ^ (4 / 5 : ℝ)) ^ (-1 : ℝ)) *
            Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) := by push_cast; ring
      _ = (2 * IntegerProductTail.productConstant 2 * (D : ℝ) ^ 2) * (N : ℝ) ^ (6 / 5 : ℝ) *
            Real.log (2 * (N : ℝ) ^ (4 / 5 : ℝ)) := by rw [hpow]
      _ ≤ (2 * IntegerProductTail.productConstant 2 * (D : ℝ) ^ 2) * (N : ℝ) ^ (6 / 5 : ℝ) *
            (logConstant * ((L + 1 : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring
  have hsecond : 2 * (2 * (D * N) * (D * (L + 1) + 1) : ℕ) * (N : ℝ) ^ (1 / 10 : ℝ) ≤
      (4 * (D : ℝ) * (D + 1)) * ((L + 1 : ℕ) : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ) := by
    have hDb : ((D * (L + 1) + 1 : ℕ) : ℝ) ≤ (D + 1 : ℝ) * ((L + 1 : ℕ) : ℝ) := by
      push_cast at hb ⊢
      nlinarith
    calc
      _ = (4 * (D : ℝ) * (D * (L + 1) + 1 : ℕ)) * ((N : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ)) := by
        push_cast
        ring
      _ ≤ (4 * (D : ℝ) * ((D + 1 : ℝ) * ((L + 1 : ℕ) : ℝ))) * (N : ℝ) ^ (6 / 5 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hDb (by positivity)) hsmall (by positivity) (by positivity)
      _ = _ := by ring
  dsimp only [coefficient]
  nlinarith [hfirst, hsecond]

theorem uniform_bound (C : ℝ) (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ),
      (∀ X ∈ F, ∀ i, X i ∈ Ico (base i) (base i + D * N)) →
      (∀ X ∈ F, 1 ≤ H X ∧ H X ≤ D * (L + 1)) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X) →
      (∀ X ∈ F, ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ D * N ∧ ((n : ℤ) - X i).natAbs ≤ R) →
      (∀ X ∈ F, ∀ i, Function.Injective (data (U X i))) →
      (∀ X ∈ F, Pairwise (fun i j ↦ Disjoint (space (U X i)) (space (U X j)))) →
      (∀ X ∈ F, (N : ℝ) ^ (6 / 5 : ℝ) < (topProduct (U X) (H X) 3 : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (6 / 5 + ε) := by
  obtain ⟨NS, hs⟩ := TernaryGroupCounts.strong_uniform 2 (1 / 10) (by norm_num)
  obtain ⟨NF, _hNF, hf⟩ := forcing_scale C D
  obtain ⟨NL, _hNL, hl⟩ := pair_threshold_log C
  obtain ⟨NP, _hNP, hp⟩ := plane_length_factor C D (coefficient D) (coefficient_nonneg D) 1 ε hε
  refine ⟨max 2 (max NS (max NF (max NL NP))), by omega, ?_⟩
  intro N hN L R hband hR F U H base hbox hH hwidth hvalues hinj hdirect hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have htail1 : 1 ≤ (N : ℝ) ^ (4 / 5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hforce (X : Fin 3 → ℕ) (hX : X ∈ F) := hf N (by omega) L (H X) hband (hH X hX).2
  have hforcing (X : Fin 3 → ℕ) (hX : X ∈ F) :
      6 * (D * N) * H X ^ 2 < topProduct (U X) (H X) 3 := by
    exact_mod_cast (hforce X hX).1.trans (hlarge X hX)
  have ht (X : Fin 3 → ℕ) (hX : X ∈ F) :
      ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 3 < (topProduct (U X) (H X) 3 : ℝ) ^ 2 := by
    have heq : ((N : ℝ) ^ (4 / 5 : ℝ)) ^ 3 = ((N : ℝ) ^ (6 / 5 : ℝ)) ^ 2 := by
      rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_mul_natCast hn.le]
      congr 1
      norm_num
    rw [heq]
    exact pow_lt_pow_left₀ (hlarge X hX) (Real.rpow_nonneg hn.le _) (by decide)
  let V : ℕ := 2 * (D * N) * (D * (L + 1) + 1)
  have hupper (X : Fin 3 → ℕ) (hX : X ∈ F) :
      2 * (D * N) * (H X + 1) ≤ N ^ 2 ∧ (2 * (D * N) * (H X + 1) : ℕ) ≤ (V : ℝ) := by
    refine ⟨(hforce X hX).2, ?_⟩
    have hu : 2 * (D * N) * (H X + 1) ≤ V :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right (hH X hX).2 1)
    exact_mod_cast hu
  have hbound := hs N (by omega) F U H (fun _ ↦ D * N) base (D * N) R
    ((N : ℝ) ^ (4 / 5 : ℝ)) V htail1 (Nat.cast_nonneg V) hbox
    (fun X hX ↦ (hH X hX).1) hwidth hvalues hinj hdirect
    (fun X hX ↦ ⟨hforcing X hX, ht X hX⟩) hupper
  have hbracket := numeric_bracket N L D (by omega) (hl N (by omega) L hband)
  have hpoly : coefficient D * ((TernaryOffsetPlanes.planePool R).card : ℝ) *
      (2 * R + 1 : ℕ) ^ 6 * ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ ε := by
    simpa only [pow_one] using hp N (by omega) L R hband hR
  calc
    _ ≤ ((TernaryOffsetPlanes.planePool R).card : ℝ) * (2 * R + 1 : ℕ) ^ 6 *
        (coefficient D * ((L + 1 : ℕ) : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ)) := hbound.trans
      (mul_le_mul_of_nonneg_left hbracket (by positivity))
    _ = (coefficient D * ((TernaryOffsetPlanes.planePool R).card : ℝ) *
        (2 * R + 1 : ℕ) ^ 6 * ((L + 1 : ℕ) : ℝ)) * (N : ℝ) ^ (6 / 5 : ℝ) := by ring
    _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (6 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_right hpoly (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.TernaryStrongCritical
