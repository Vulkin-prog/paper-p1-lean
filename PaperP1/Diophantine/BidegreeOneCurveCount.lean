module

public import PaperP1.Diophantine.BidegreeOneFibreCount

/-! # Uniform polynomial-coefficient counts for the bidegree-one auxiliary case -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BidegreeOneCurveCount

open Finset Polynomial MvPolynomial PaperP1.BidegreeOneFibreCount

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def solutions {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (A H : ℕ) : Finset Point :=
  ((Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-(A : ℤ)) A) ×ˢ
    (Fintype.piFinset fun _ : Fin 2 ↦ Finset.Icc (-(H : ℤ)) H)).filter (Good C f g d h)

def realSolutions {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (A H : ℝ) : Finset Point :=
  solutions C f g d h ⌊A⌋₊ ⌊H⌋₊

theorem integer_box_floor (z : ℤ) (H : ℝ) (hH : 0 ≤ H) :
    z ∈ Finset.Icc (-(⌊H⌋₊ : ℤ)) ⌊H⌋₊ ↔ |(z : ℝ)| ≤ H := by
  have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
    cases z with
    | ofNat n => simp
    | negSucc n =>
      simp
      rw [abs_of_nonpos (by have := Nat.cast_nonneg n (α := ℝ); linarith)]
      ring
  rw [mem_Icc, ← abs_le, Int.abs_eq_natAbs]
  constructor
  · intro hz
    have hn : z.natAbs ≤ ⌊H⌋₊ := by exact_mod_cast hz
    simpa only [habs] using (Nat.le_floor_iff hH).mp hn
  · intro hz
    have hn : z.natAbs ≤ ⌊H⌋₊ := (Nat.le_floor_iff hH).mpr (by simpa only [habs] using hz)
    exact_mod_cast hn

theorem mem_realSolutions {ell : ℕ} (C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ)
    (f g : ℤ[X]) (d : ℕ) (h : ℤ) (A H : ℝ) (hA : 0 ≤ A) (hH : 0 ≤ H) (s : Point) :
    s ∈ realSolutions C f g d h A H ↔
      (∀ i, |(s.1 i : ℝ)| ≤ A) ∧ (∀ i, |(s.2 i : ℝ)| ≤ H) ∧ Good C f g d h s := by
  simp only [realSolutions, solutions, mem_filter, mem_product, Fintype.mem_piFinset,
    integer_box_floor _ A hA, integer_box_floor _ H hH, and_assoc]

theorem integer_coefficient_bound (f : ℤ[X]) (N : ℕ) (hN : 1 ≤ N) (A₀ : ℝ)
    (hf : ∀ j, ((f.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) :
    ∀ j, (f.coeff j).natAbs ≤ N ^ ⌈A₀⌉₊ := by
  have hpow : (N : ℝ) ^ A₀ ≤ ((N ^ ⌈A₀⌉₊ : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast, Nat.cast_pow] using
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1 : ℝ) ≤ N) (Nat.le_ceil A₀)
  intro j
  exact_mod_cast (hf j).trans hpow

theorem coefficient_uniform_scale_count (d A₀ : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (∀ j, (f.coeff j).natAbs ≤ N ^ A₀) → (∀ j, (g.coeff j).natAbs ≤ N ^ A₀) →
        ∀ ell : ℕ, ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, ∀ h : ℤ, ∀ S : Finset Point,
          (∀ s ∈ S, Good C f g d h s) → ((S.image (chosenScale f g d)).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.ResultantHeight.coefficient_uniform_denominator_count d A₀ hd ε hε
  refine ⟨N₀, ?_⟩
  intro N hN f g hf hg hR hR' hfc hgc ell C h S hS
  apply hN₀ N hN f g hf hg hR hR' hfc hgc
  intro q hq
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hq
  have hgood := hS s hs
  obtain ⟨hleft, hright⟩ := form_divisibilities hgood
  refine ⟨chosenScale_ne_zero hd hf hg hR hR' hgood, s.2 0, s.2 1, hgood.2.1, ?_, ?_⟩
  · simpa only [two_coordinates] using hleft
  · simpa only [two_coordinates] using hright

theorem polynomial_coefficient_count (ell k d A₀ : ℕ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (∀ j, (f.coeff j).natAbs ≤ N ^ A₀) → (∀ j, (g.coeff j).natAbs ≤ N ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ H : ℕ, 1 ≤ H → ∀ S : Finset Point,
            (∀ s ∈ S, Good C f g d h s) → (∀ s ∈ S, ∀ i, |s.2 i| ≤ (H : ℤ)) →
              (S.card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨Nq, hNq⟩ := coefficient_uniform_scale_count d A₀ hd (ε / 2) (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) (3 * ((k + d * ell : ℕ) : ℝ)))
      (ε / 2) (by positivity)
  refine ⟨max 1 (max Nq Nc), ?_⟩
  intro N hN f g hf hg hR hR' hfc hgc C hC h hh H hH S hS hbox
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hscales := hNq N (by omega) f g hf hg hR hR' hfc hgc ell C h S hS
  have hconstant : 3 * ((k + d * ell : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hgrid : (2 * (H : ℝ) + 1) ≤ 3 * H := by
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hfinite : (S.card : ℝ) ≤ ((S.image (chosenScale f g d)).card : ℝ) *
      ((k + d * ell : ℕ) : ℝ) * (2 * H + 1) := by
    have h := count_by_scales C f g d h hd hh hf hg hR hR' hC hdegree H S hS hbox
    have h' : (S.card : ℝ) ≤ ((S.image (chosenScale f g d)).card : ℝ) *
        (((k + d * ell : ℕ) : ℝ) * (2 * H + 1)) := by exact_mod_cast h
    simpa only [mul_assoc] using h'
  calc
    _ ≤ ((S.image (chosenScale f g d)).card : ℝ) * ((k + d * ell : ℕ) : ℝ) * (2 * H + 1) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * ((k + d * ell : ℕ) : ℝ) * (3 * H) := by gcongr
    _ = (3 * ((k + d * ell : ℕ) : ℝ)) * (N : ℝ) ^ (ε / 2) * H := by ring
    _ ≤ ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * H := by gcongr
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem actual_solutions_count (ell k d A₀ : ℕ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (∀ j, (f.coeff j).natAbs ≤ N ^ A₀) → (∀ j, (g.coeff j).natAbs ≤ N ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℕ, 1 ≤ H →
            ((solutions C f g d h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := polynomial_coefficient_count ell k d A₀ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN f g hf hg hR hR' hfc hgc C hC h hh A H hH
  apply hN₀ N hN f g hf hg hR hR' hfc hgc C hC h hh H hH
  · intro s hs
    exact (mem_filter.mp hs).2
  · intro s hs i
    have hblock := (mem_product.mp (mem_filter.mp hs).1).2
    exact abs_le.mpr (mem_Icc.mp ((Fintype.mem_piFinset.mp hblock) i))

theorem actual_real_solutions_count (ell k d : ℕ) (A₀ : ℝ) (hd : 0 < d)
    (hdegree : 0 < k + d * ell) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ f g : ℤ[X], f.natDegree ≤ d → g.natDegree ≤ d →
      f.resultant g d d ≠ 0 → (f.reflect d).resultant (g.reflect d) d d ≠ 0 →
      (∀ j, ((f.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      (∀ j, ((g.coeff j).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
        ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ, (∀ i, (C i).IsHomogeneous k) →
          ∀ h : ℤ, h ≠ 0 → ∀ A H : ℝ, 0 ≤ A → 1 ≤ H →
            ((realSolutions C f g d h A H).card : ℝ) ≤ (N : ℝ) ^ ε * H := by
  obtain ⟨N₀, hN₀⟩ := actual_solutions_count ell k d ⌈A₀⌉₊ hd hdegree ε hε
  refine ⟨max 1 N₀, ?_⟩
  intro N hN f g hf hg hR hR' hfc hgc C hC h hh A H _hA hH
  have hH0 : 0 ≤ H := by linarith
  have hfloor : 1 ≤ ⌊H⌋₊ := (Nat.one_le_floor_iff H).mpr hH
  have hcount := hN₀ N (by omega) f g hf hg hR hR'
    (integer_coefficient_bound f N (by omega) A₀ hfc) (integer_coefficient_bound g N (by omega) A₀ hgc)
    C hC h hh ⌊A⌋₊ ⌊H⌋₊ hfloor
  exact hcount.trans (mul_le_mul_of_nonneg_left (Nat.floor_le hH0) (Real.rpow_nonneg (Nat.cast_nonneg N) ε))

end PaperP1.BidegreeOneCurveCount
