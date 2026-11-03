module

public import PaperP1.Arithmetic.TernaryTopProducts
public import PaperP1.Arithmetic.CRTProductRange
public import PaperP1.Arithmetic.TernaryOffsetPlanes
public import PaperP1.Arithmetic.PlaneProductCover

/-! # Actual ternary groups supply the finite CRT certificates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupCertificates

open Finset PaperP1.TernaryPrimeGroups PaperP1.TernaryTopProducts
  PaperP1.TernaryGroupDeterminants PaperP1.FiniteEvenSquareClasses PaperP1.TripleCross

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem selected_certificate {k H R : ℕ} {U : Fin 3 → Finset ℕ} (X : Fin 3 → ℕ)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hbox : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (v : Fin k → Fin 3 → ℕ) (hv : Function.Injective v) (hmem : ∀ j, v j ∈ supportPool U)
    (base : Fin 3 → ℕ) (N : ℕ) (hX : ∀ i, X i ∈ Ico (base i) (base i + N)) :
    X ∈ CRTProductCover.productCentres k 3 base N R (∏ j, group H (v j)) := by
  let q : Fin k → ℕ := fun j ↦ group H (v j)
  let w : Fin k → Fin 3 → ℤ := fun j i ↦ (v j i : ℤ) - X i
  have hQ : 0 < ∏ j, q j := prod_pos (fun j _ ↦ group_pos H (v j))
  apply (CRTProductCover.mem_productCentres k 3 base N R _ hQ X).mpr
  refine ⟨hX, q, w, rfl, ?_, ?_, ?_⟩
  · intro j i
    exact hbox i (v j i) ((mem_supportPool U (v j)).mp (hmem j) i)
  · intro i j hij
    exact group_coprime hwidth (hmem i) (hmem j) (fun heq ↦ hij (hv heq))
  · intro j i
    have hd := Int.natCast_dvd_natCast.mpr (group_dvd_value H (v j) i)
    have heq : (X i : ℤ) + w j i = (v j i : ℤ) := by dsimp [w]; ring
    rw [heq]
    exact hd

theorem top_product_certificate {H k R : ℕ} {U : Fin 3 → Finset ℕ} (X : Fin 3 → ℕ)
    (hp : 0 < topProduct U H k)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hbox : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (base : Fin 3 → ℕ) (N : ℕ) (hX : ∀ i, X i ∈ Ico (base i) (base i + N)) :
    X ∈ CRTProductCover.productCentres k 3 base N R (topProduct U H k) := by
  obtain ⟨S, hsub, hcard, hprod⟩ := attained U H k hp
  obtain ⟨v, hv, hmem, heq⟩ := enumerate_selection U H k S hsub hcard
  have hc := selected_certificate X hwidth hbox v hv (fun j ↦ (mem_filter.mp (hmem j)).1) base N hX
  rwa [heq, ← hprod] at hc

theorem some_large_pair (g : Fin 3 → ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hlarge : T ^ 3 < ((g 0 : ℝ) * g 1 * g 2) ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ T < (g i : ℝ) * g j := by
  by_cases h01 : T < (g 0 : ℝ) * g 1
  · exact ⟨0, 1, by decide, h01⟩
  by_cases h02 : T < (g 0 : ℝ) * g 2
  · exact ⟨0, 2, by decide, h02⟩
  by_cases h12 : T < (g 1 : ℝ) * g 2
  · exact ⟨1, 2, by decide, h12⟩
  have hbound : ((g 0 : ℝ) * g 1 * g 2) ^ 2 ≤ T ^ 3 := by
    calc
      _ = ((g 0 : ℝ) * g 1) * ((g 0 : ℝ) * g 2) * ((g 1 : ℝ) * g 2) := by ring
      _ ≤ (T * T) * T := mul_le_mul
        (mul_le_mul (le_of_not_gt h01) (le_of_not_gt h02) (by positivity) hT)
        (le_of_not_gt h12) (by positivity) (mul_nonneg hT hT)
      _ = _ := by ring
  exact False.elim (not_lt_of_ge hbound hlarge)

theorem large_triple_certificate {U : Fin 3 → Finset ℕ} {A H R : ℕ} (X : Fin 3 → ℕ)
    (hH : 1 ≤ H)
    (hwidth : ∀ i, ∀ n ∈ U i, ∀ m ∈ U i, ((n : ℤ) - m).natAbs ≤ H)
    (hpos : ∀ i, ∀ n ∈ U i, 0 < n) (hmax : ∀ i, ∀ n ∈ U i, n ≤ A)
    (hinj : ∀ i, Function.Injective (data (U i)))
    (hdirect : Pairwise (fun i j ↦ Disjoint (space (U i)) (space (U j))))
    (hbox : ∀ i, ∀ n ∈ U i, ((n : ℤ) - X i).natAbs ≤ R)
    (v : Fin 3 → Fin 3 → ℕ) (hv : Function.Injective v) (hmem : ∀ j, v j ∈ supportPool U)
    (hlarge : 6 * A * H ^ 2 < group H (v 0) * group H (v 1) * group H (v 2))
    (T : ℝ) (hT : 0 ≤ T)
    (htail : T ^ 3 < ((group H (v 0) : ℝ) * group H (v 1) * group H (v 2)) ^ 2)
    (base : Fin 3 → ℕ) (N : ℕ) (hX : ∀ i, X i ∈ Ico (base i) (base i + N)) :
    ∃ p : ℕ × ℕ, 0 < p.1 ∧ 0 < p.2 ∧ T < (p.1 : ℝ) * p.2 ∧
      p.1 * p.2 ≤ 2 * A * (H + 1) ∧
      X ∈ PlaneProductCover.pairCentres base N R (TernaryOffsetPlanes.planePool R) p := by
  obtain ⟨P, hP, _hPne, hcoord, hplane⟩ := TernaryOffsetPlanes.forced_offset_plane
    hH hwidth hpos hmax hinj hdirect hbox (hmem 0) (hmem 1) (hmem 2)
    (fun heq ↦ (by decide : (0 : Fin 3) ≠ 1) (hv heq))
    (fun heq ↦ (by decide : (0 : Fin 3) ≠ 2) (hv heq))
    (fun heq ↦ (by decide : (1 : Fin 3) ≠ 2) (hv heq)) hlarge
  obtain ⟨i, j, hij, hprod⟩ := some_large_pair (fun t ↦ group H (v t)) T hT htail
  let p : ℕ × ℕ := (group H (v i), group H (v j))
  let w : Fin 2 → Fin 3 → ℤ := fun t a ↦ ((![v i, v j] t) a : ℤ) - X a
  have hcopij := group_coprime hwidth (hmem i) (hmem j) (fun heq ↦ hij (hv heq))
  have hcop : Pairwise (fun s t ↦ Nat.Coprime (![p.1, p.2] s) (![p.1, p.2] t)) := by
    intro s t hst
    fin_cases s <;> fin_cases t
    · exact False.elim (hst rfl)
    · simpa [p] using hcopij
    · simpa [p] using hcopij.symm
    · exact False.elim (hst rfl)
  refine ⟨p, group_pos H (v i), group_pos H (v j), hprod,
    group_product_le hwidth hpos hmax hinj hdirect (hmem i) (hmem j) (fun heq ↦ hij (hv heq)), ?_⟩
  apply PlaneProductCover.mem_pairCentres_of base N R _ p X hX P hP (hcoord 2) hplane w
  · intro t a
    fin_cases t
    · exact hbox a (v i a) ((mem_supportPool U (v i)).mp (hmem i) a)
    · exact hbox a (v j a) ((mem_supportPool U (v j)).mp (hmem j) a)
  · exact hcop
  · intro t a
    have heq : (X a : ℤ) + w t a = ((![v i, v j] t) a : ℤ) := by dsimp [w]; ring
    rw [heq]
    fin_cases t
    · exact Int.natCast_dvd_natCast.mpr (group_dvd_value H (v i) a)
    · exact Int.natCast_dvd_natCast.mpr (group_dvd_value H (v j) a)

end PaperP1.TernaryGroupCertificates
