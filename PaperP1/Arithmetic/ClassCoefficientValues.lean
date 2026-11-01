module

public import PaperP1.Arithmetic.RelativeSquarefreeParts
public import PaperP1.Arithmetic.PhysicalClassData

/-! # Literal finite coefficient choices for a bounded physical class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ClassCoefficientValues

open Finset PaperP1.PhysicalClassData PaperP1.RelativeSquarefreeParts PaperP1.SmallPrimeBudget

def values (H m E : ℕ) : Finset ℕ := (primorial H).divisors.biUnion fun a ↦
  m.divisors.biUnion fun b ↦ (Icc 1 E).image fun e ↦ a * b * e * m

theorem mem_values (H m E D : ℕ) :
    D ∈ values H m E ↔ ∃ a ∈ (primorial H).divisors, ∃ b ∈ m.divisors,
      ∃ e ∈ Icc 1 E, a * b * e * m = D := by
  simp only [values, mem_biUnion, mem_image]

theorem values_pos {H m E D : ℕ} (hm : 0 < m) (hD : D ∈ values H m E) : 0 < D := by
  obtain ⟨a, ha, b, hb, e, he, rfl⟩ := (mem_values H m E D).mp hD
  have ha := Nat.pos_of_mem_divisors ha
  have hb := Nat.pos_of_mem_divisors hb
  have he := (mem_Icc.mp he).1
  positivity

theorem card_values (H m E : ℕ) :
    (values H m E).card ≤ (primorial H).divisors.card * m.divisors.card * E := by
  calc
    _ ≤ ∑ a ∈ (primorial H).divisors,
        (m.divisors.biUnion fun b ↦ (Icc 1 E).image fun e ↦ a * b * e * m).card := card_biUnion_le
    _ ≤ ∑ _a ∈ (primorial H).divisors, m.divisors.card * E := by
      apply sum_le_sum
      intro a _
      calc
        _ ≤ ∑ b ∈ m.divisors, ((Icc 1 E).image fun e ↦ a * b * e * m).card := card_biUnion_le
        _ ≤ ∑ _b ∈ m.divisors, E := by
          apply sum_le_sum
          intro b _
          exact card_image_le.trans (by simp)
        _ = _ := by simp
    _ = _ := by simp [mul_assoc]

theorem square_witness (H m p E : ℕ) (hm : 0 < m) (hp : 0 < p)
    (he : residualPart H (m * p) m ≤ E) :
    ∃ D ∈ values H m E, IsSquare (D * p) := by
  let a := smallOddPart H (m * p)
  let b := sourcePart H (m * p) m
  let e := residualPart H (m * p) m
  refine ⟨a * b * e * m, (mem_values H m E _).mpr ?_, square_equation H m p hm.ne' hp.ne'⟩
  exact ⟨a, Nat.mem_divisors.mpr ⟨smallOddPart_dvd_primorial H (m * p), (primorial_pos H).ne'⟩,
    b, Nat.mem_divisors.mpr ⟨sourcePart_dvd H (m * p) m, hm.ne'⟩,
    e, mem_Icc.mpr ⟨residualPart_pos H (m * p) m, he⟩, rfl⟩

theorem integer_square (H m p E : ℕ) (hm : 0 < m) (hp : 0 < p)
    (he : residualPart H (m * p) m ≤ E) :
    ∃ D ∈ values H m E, IsSquare ((D : ℤ) * p) := by
  obtain ⟨D, hD, r, hr⟩ := square_witness H m p E hm hp he
  refine ⟨D, hD, (r : ℤ), ?_⟩
  exact_mod_cast hr

end PaperP1.ClassCoefficientValues
