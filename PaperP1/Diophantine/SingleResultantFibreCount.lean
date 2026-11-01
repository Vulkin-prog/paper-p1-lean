module

public import PaperP1.Diophantine.ReflectedResultants
public import PaperP1.Diophantine.BidegreeOneCurveCount

/-! # A single homogeneous resultant controls the actual primitive scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SingleResultantFibreCount

open Finset Polynomial MvPolynomial PaperP1.BidegreeOneFibreCount

theorem scale_count {ell : ℕ} {C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ}
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hR : f.resultant g d d ≠ 0)
    (S : Finset Point) (hS : ∀ s ∈ S, Good C f g d h s) :
    (S.image (chosenScale f g d)).card ≤ 2 * (f.resultant g d d).natAbs.divisors.card := by
  have hsub : S.image (chosenScale f g d) ⊆ PaperP1.PrimitiveDenominators.signedDivisors (f.resultant g d d) := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
    have hgood := hS s hs
    obtain ⟨hleft, hright⟩ := form_divisibilities hgood
    apply PaperP1.PrimitiveDenominators.mem_signedDivisors hR
    exact PaperP1.ReflectedResultants.primitive_resultant_divisor f g d hd hf hg (s.2 0) (s.2 1)
      (chosenScale f g d s) hgood.2.1 (by simpa only [two_coordinates] using hleft)
        (by simpa only [two_coordinates] using hright)
  exact (card_le_card hsub).trans (PaperP1.PrimitiveDenominators.signedDivisors_card _)

theorem finite_count {ell k : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (hd : 0 < d) (hh : h ≠ 0)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d) (hR : f.resultant g d d ≠ 0)
    (hC : ∀ i, (C i).IsHomogeneous k) (hdegree : 0 < k + d * ell)
    (H : ℕ) (S : Finset Point) (hS : ∀ s ∈ S, Good C f g d h s)
    (hbox : ∀ s ∈ S, ∀ i, |s.2 i| ≤ (H : ℤ)) :
    S.card ≤ 2 * (f.resultant g d d).natAbs.divisors.card * (k + d * ell) * (2 * H + 1) := by
  have hR' := PaperP1.ReflectedResultants.reflected_resultant_ne_zero f g d hR
  have hbase := count_by_scales C f g d h hd hh hf hg hR hR' hC hdegree H S hS hbox
  have hcount := Nat.mul_le_mul_right ((k + d * ell) * (2 * H + 1)) (scale_count f g d h hd hf hg hR S hS)
  exact hbase.trans (by simpa only [Nat.mul_assoc] using hcount)

theorem actual_real_solutions_count (ell k d : ℕ) (A₀ : ℝ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 →
      (∀ j, ((f.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ j, ((g.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 0 ≤ A → 1 ≤ H →
            ((PaperP1.BidegreeOneCurveCount.realSolutions C f g d h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.BidegreeOneCurveCount.actual_real_solutions_count ell k d A₀ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN f g hf hg hR hfc hgc C hC h hh A H hA hH
  exact hN₀ N hN f g hf hg hR (PaperP1.ReflectedResultants.reflected_resultant_ne_zero f g d hR)
    hfc hgc C hC h hh A H hA hH

theorem coprime_actual_real_solutions_count (ell k d : ℕ) (A₀ : ℝ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      (f.natDegree = d ∨ g.natDegree = d) →
      IsCoprime (f.map (Int.castRingHom ℚ)) (g.map (Int.castRingHom ℚ)) →
      (∀ j, ((f.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ j, ((g.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 0 ≤ A → 1 ≤ H →
            ((PaperP1.BidegreeOneCurveCount.realSolutions C f g d h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := actual_real_solutions_count ell k d A₀ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN f g hf hg hfull hcop hfc hgc C hC h hh A H hA hH
  exact hN₀ N hN f g hf hg
    (PaperP1.ResultantDivisibility.integer_padded_resultant_ne_zero f g d hd hf hg hfull hcop)
    hfc hgc C hC h hh A H hA hH

end PaperP1.SingleResultantFibreCount
