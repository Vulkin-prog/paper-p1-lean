module

public import PaperP1.Diophantine.BidegreeOneElimination
public import Mathlib.Tactic.FinCases

/-! # Actual primitive solutions on an auxiliary curve linear in one pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BidegreeOneFibreCount

open Finset Polynomial MvPolynomial PaperP1.BidegreeOneElimination

abbrev Point := (Fin 2 → ℤ) × (Fin 2 → ℤ)

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def chosenScale (f g : ℤ[X]) (d : ℕ) (s : Point) : ℤ :=
  scale (s.1 0) (s.1 1) (eval s.2 (f.homogenize d)) (eval s.2 (g.homogenize d))

def Good {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (s : Point) : Prop :=
  (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧
    (s.2 0).natAbs.Coprime (s.2 1).natAbs ∧
      s.1 0 * eval s.2 (f.homogenize d) + s.1 1 * eval s.2 (g.homogenize d) = 0 ∧
        original C s.1 s.2 = h

theorem two_coordinates (z : Fin 2 → ℤ) : ![z 0, z 1] = z := by
  funext i
  fin_cases i <;> rfl

theorem scale_relations {ell : ℕ} {C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ}
    {f g : ℤ[X]} {d : ℕ} {h : ℤ} {s : Point} (hs : Good C f g d h s) :
    chosenScale f g d s * s.1 0 = eval s.2 (g.homogenize d) ∧
      chosenScale f g d s * s.1 1 = -eval s.2 (f.homogenize d) :=
  scale_equations _ _ _ _ hs.1 hs.2.2.1

theorem form_divisibilities {ell : ℕ} {C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ}
    {f g : ℤ[X]} {d : ℕ} {h : ℤ} {s : Point} (hs : Good C f g d h s) :
    chosenScale f g d s ∣ eval s.2 (f.homogenize d) ∧
      chosenScale f g d s ∣ eval s.2 (g.homogenize d) := by
  obtain ⟨hfirst, hsecond⟩ := scale_relations hs
  refine ⟨⟨-s.1 1, ?_⟩, ⟨s.1 0, hfirst.symm⟩⟩
  linear_combination hsecond

theorem chosenScale_ne_zero {ell : ℕ} {C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ}
    {f g : ℤ[X]} {d : ℕ} {h : ℤ} {s : Point} (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hR : f.resultant g d d ≠ 0) (hR' : (f.reflect d).resultant (g.reflect d) d d ≠ 0)
    (hs : Good C f g d h s) : chosenScale f g d s ≠ 0 := by
  obtain ⟨hleft, hright⟩ := form_divisibilities hs
  have hdiv := PaperP1.ResultantDivisibility.primitive_resultant_product f g d hd hf hg
    (s.2 0) (s.2 1) (chosenScale f g d s) hs.2.1
    (by simpa only [two_coordinates] using hleft) (by simpa only [two_coordinates] using hright)
  intro hz
  rw [hz, zero_dvd_iff] at hdiv
  exact mul_ne_zero hR hR' hdiv

theorem scale_count {ell : ℕ} {C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ}
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hR : f.resultant g d d ≠ 0) (hR' : (f.reflect d).resultant (g.reflect d) d d ≠ 0)
    (S : Finset Point) (hS : ∀ s ∈ S, Good C f g d h s) :
    (S.image (chosenScale f g d)).card ≤
      2 * (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs.divisors.card := by
  apply PaperP1.ResultantDivisibility.finite_denominator_count f g d hd hf hg hR hR'
  intro q hq
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
  have hgood := hS s hs
  obtain ⟨hleft, hright⟩ := form_divisibilities hgood
  refine ⟨chosenScale_ne_zero hd hf hg hR hR' hgood, s.2 0, s.2 1, hgood.2.1, ?_, ?_⟩
  · simpa only [two_coordinates] using hleft
  · simpa only [two_coordinates] using hright

theorem fixed_scale_card {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h q : ℤ) (hq : q ≠ 0) (H : ℕ) (S : Finset Point)
    (hS : ∀ s ∈ S, Good C f g d h s) (hbox : ∀ s ∈ S, ∀ i, |s.2 i| ≤ (H : ℤ)) :
    ((S.filter fun s ↦ chosenScale f g d s = q).card) ≤
      (PaperP1.BivariateGridCount.level (eliminant C (f.homogenize d) (g.homogenize d))
        (q ^ ell * h) (Finset.Icc (-(H : ℤ)) H)).card := by
  apply card_le_card_of_injOn Prod.snd
  · intro s hs
    obtain ⟨hsS, hsq⟩ := mem_filter.mp hs
    have hgood := hS s hsS
    obtain ⟨hfirst, hsecond⟩ := scale_relations hgood
    rw [hsq] at hfirst hsecond
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr (fun i ↦ mem_Icc.mpr (abs_le.mp (hbox s hsS i))), ?_⟩
    exact eliminant_equation C _ _ s.1 s.2 q h hfirst hsecond hgood.2.2.2
  · intro s hs t ht heq
    change s.2 = t.2 at heq
    obtain ⟨hsS, hsq⟩ := mem_filter.mp hs
    obtain ⟨htS, htq⟩ := mem_filter.mp ht
    obtain ⟨hsfirst, hssecond⟩ := scale_relations (hS s hsS)
    obtain ⟨htfirst, htsecond⟩ := scale_relations (hS t htS)
    rw [hsq] at hsfirst hssecond
    rw [htq] at htfirst htsecond
    have h0 : s.1 0 = t.1 0 := mul_left_cancel₀ hq
      (hsfirst.trans ((congrArg (fun z : Fin 2 → ℤ ↦ eval z (g.homogenize d)) heq).trans htfirst.symm))
    have h1 : s.1 1 = t.1 1 := mul_left_cancel₀ hq
      (hssecond.trans ((congrArg (fun z : Fin 2 → ℤ ↦ -eval z (f.homogenize d)) heq).trans htsecond.symm))
    apply Prod.ext _ heq
    funext i
    fin_cases i
    · exact h0
    · exact h1

theorem count_by_scales {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (hd : 0 < d) (hh : h ≠ 0)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hR : f.resultant g d d ≠ 0) (hR' : (f.reflect d).resultant (g.reflect d) d d ≠ 0)
    (hC : ∀ i, (C i).IsHomogeneous k) (hdegree : 0 < k + d * ell)
    (H : ℕ) (S : Finset Point) (hS : ∀ s ∈ S, Good C f g d h s)
    (hbox : ∀ s ∈ S, ∀ i, |s.2 i| ≤ (H : ℤ)) :
    S.card ≤ (S.image (chosenScale f g d)).card * ((k + d * ell) * (2 * H + 1)) := by
  calc
    _ = ∑ q ∈ S.image (chosenScale f g d), (S.filter fun s ↦ chosenScale f g d s = q).card :=
      card_eq_sum_card_image _ _
    _ ≤ ∑ _q ∈ S.image (chosenScale f g d), (k + d * ell) * (2 * H + 1) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
      have hq0 := chosenScale_ne_zero hd hf hg hR hR' (hS s hs)
      exact (fixed_scale_card C f g d h _ hq0 H S hS hbox).trans
        (level_box_bound C _ _ hC (Polynomial.isHomogeneous_homogenize f)
          (Polynomial.isHomogeneous_homogenize g) hdegree _ h hq0 hh H)
    _ = _ := by simp

theorem finite_count {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (hd : 0 < d) (hh : h ≠ 0)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hR : f.resultant g d d ≠ 0) (hR' : (f.reflect d).resultant (g.reflect d) d d ≠ 0)
    (hC : ∀ i, (C i).IsHomogeneous k) (hdegree : 0 < k + d * ell)
    (H : ℕ) (S : Finset Point) (hS : ∀ s ∈ S, Good C f g d h s)
    (hbox : ∀ s ∈ S, ∀ i, |s.2 i| ≤ (H : ℤ)) :
    S.card ≤ 2 * (f.resultant g d d * (f.reflect d).resultant (g.reflect d) d d).natAbs.divisors.card *
      (k + d * ell) * (2 * H + 1) := by
  have hsum := count_by_scales C f g d h hd hh hf hg hR hR' hC hdegree H S hS hbox
  refine hsum.trans ?_
  have hcount := Nat.mul_le_mul_right ((k + d * ell) * (2 * H + 1)) (scale_count f g d h hd hf hg hR hR' S hS)
  simpa only [Nat.mul_assoc] using hcount

end PaperP1.BidegreeOneFibreCount
