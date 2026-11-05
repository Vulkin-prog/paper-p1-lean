module

public import PaperP1.Diophantine.ProjectiveSmoothDeterminant
public import PaperP1.Algebra.WeightedEvaluationDeterminant

/-! # Exact size comparison forces the actual smooth projective minors to vanish -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveDeterminantVanishing

open Polynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrix (H J : ℕ) (r s : ι → ℕ) (x y : ι → Fin 2 → ℤ) : Matrix ι ι ℤ :=
  Matrix.of (fun i j ↦ x j 0 ^ r i * x j 1 ^ (H - r i) * y j 0 ^ s i * y j 1 ^ (J - s i))

theorem indexed_divisor (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (r s : ι → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (x y : ι → Fin 2 → ℤ) (hdenX : ∀ j, ¬(p : ℤ) ∣ x j 1) (hdenY : ∀ j, ¬(p : ℤ) ∣ y j 1)
    (hx : ∀ j, (p : ℤ) ∣ x j 0 - a * x j 1) (hy : ∀ j, (p : ℤ) ∣ y j 0 - b * y j 1)
    (hcurve : ∀ j, MvPolynomial.eval₂ (MvPolynomial.eval (y j)) (x j)
      (PaperP1.IntegerFactorProjectiveCurve.projective G) = 0) :
    (p : ℤ) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) ∣ (matrix H J r s x y).det := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hd := ProjectiveSmoothDeterminant.integer_smooth_dvd p (Fintype.card ι) hp G a b hG hder
    H J (fun i ↦ r (e.symm i)) (fun i ↦ s (e.symm i))
    (fun i ↦ hr (e.symm i)) (fun i ↦ hs (e.symm i))
    (fun i ↦ x (e.symm i)) (fun i ↦ y (e.symm i))
    (fun i ↦ hdenX (e.symm i)) (fun i ↦ hdenY (e.symm i))
    (fun i ↦ hx (e.symm i)) (fun i ↦ hy (e.symm i)) (fun i ↦ hcurve (e.symm i))
  have he : Matrix.reindex e e (matrix H J r s x y) =
      ProjectiveSmoothDeterminant.monomialMatrix H J
        (fun i ↦ r (e.symm i)) (fun i ↦ s (e.symm i))
        (fun i ↦ x (e.symm i) 0) (fun i ↦ y (e.symm i) 0)
        (fun i ↦ x (e.symm i) 1) (fun i ↦ y (e.symm i) 1) := by
    ext i j
    rfl
  rw [← he, Matrix.det_reindex_self] at hd
  exact hd

omit [Fintype ι] [DecidableEq ι] in
theorem entry_bound (H J : ℕ) (r s : ι → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (x y : ι → Fin 2 → ℤ)
    (hx : ∀ j c, |(x j c : ℝ)| ≤ L) (hy : ∀ j c, |(y j c : ℝ)| ≤ Y) (i j : ι) :
    |((matrix H J r s x y i j : ℤ) : ℝ)| ≤ L ^ H * Y ^ J := by
  simp only [matrix, Matrix.of_apply, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow]
  calc
    _ ≤ L ^ r i * L ^ (H - r i) * Y ^ s i * Y ^ (J - s i) := by
      gcongr
      · exact hx j 0
      · exact hx j 1
      · exact hy j 0
      · exact hy j 1
    _ = (L ^ r i * L ^ (H - r i)) * (Y ^ s i * Y ^ (J - s i)) := by ring
    _ = _ := by rw [← pow_add, ← pow_add, Nat.add_sub_of_le (hr i), Nat.add_sub_of_le (hs i)]

theorem determinant_bound (H J : ℕ) (r s : ι → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (x y : ι → Fin 2 → ℤ)
    (hx : ∀ j c, |(x j c : ℝ)| ≤ L) (hy : ∀ j c, |(y j c : ℝ)| ≤ Y) :
    |(((matrix H J r s x y).det : ℤ) : ℝ)| ≤
      (Fintype.card ι).factorial * (L ^ H * Y ^ J) ^ Fintype.card ι := by
  let φ := Int.castRingHom ℝ
  let M := φ.mapMatrix (matrix H J r s x y)
  have he : M.det = (((matrix H J r s x y).det : ℤ) : ℝ) := (φ.map_det _).symm
  have hentry (i j : ι) : |M i j| ≤ L ^ H * Y ^ J :=
    entry_bound H J r s hr hs L Y hL hY x y hx hy i j
  have h := PaperP1.WeightedEvaluationDeterminant.row_weight_bound M (fun _ ↦ L ^ H * Y ^ J) hentry
  rw [he] at h
  simpa only [Finset.prod_const, Finset.card_univ] using h

theorem zero_of_dvd_small (d : ℕ) (z : ℤ) (hd : (d : ℤ) ∣ z) (hsmall : |(z : ℝ)| < d) : z = 0 := by
  by_contra hn
  have hnat : d ≤ z.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_le_of_dvd_ne_zero hd hn
  have hreal : (d : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast hnat
  have hcast : (z.natAbs : ℝ) = |(z : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [hcast] at hreal
  exact (not_lt_of_ge hreal) hsmall

theorem vanishing (p : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (r s : ι → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (L Y : ℝ) (hL : 0 ≤ L) (hY : 0 ≤ Y) (x y : ι → Fin 2 → ℤ)
    (hxbox : ∀ j c, |(x j c : ℝ)| ≤ L) (hybox : ∀ j c, |(y j c : ℝ)| ≤ Y)
    (hdenX : ∀ j, ¬(p : ℤ) ∣ x j 1) (hdenY : ∀ j, ¬(p : ℤ) ∣ y j 1)
    (hx : ∀ j, (p : ℤ) ∣ x j 0 - a * x j 1) (hy : ∀ j, (p : ℤ) ∣ y j 0 - b * y j 1)
    (hcurve : ∀ j, MvPolynomial.eval₂ (MvPolynomial.eval (y j)) (x j)
      (PaperP1.IntegerFactorProjectiveCurve.projective G) = 0)
    (hsmall : (Fintype.card ι).factorial * (L ^ H * Y ^ J) ^ Fintype.card ι <
      (p : ℝ) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2)) :
    (matrix H J r s x y).det = 0 := by
  have hd := indexed_divisor p hp G a b hG hder H J r s hr hs x y hdenX hdenY hx hy hcurve
  have hsml := (determinant_bound H J r s hr hs L Y hL hY x y hxbox hybox).trans_lt hsmall
  apply zero_of_dvd_small (p ^ (Fintype.card ι * (Fintype.card ι - 1) / 2)) _
  · simpa only [Nat.cast_pow] using hd
  · simpa only [Nat.cast_pow] using hsml

end PaperP1.ProjectiveDeterminantVanishing
