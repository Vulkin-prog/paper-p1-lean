module

public import PaperP1.Diophantine.ProjectiveUnitCharts
public import PaperP1.Algebra.SmoothCurveDeterminant

/-! # Smooth projective residue-class determinants with the original homogeneous rows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveSmoothDeterminant

open Polynomial PaperP1.ProjectiveUnitCharts PaperP1.BivariateEvaluation

variable {R : Type*} [CommRing R] {k : ℕ}

def monomialMatrix (H J : ℕ) (r s : Fin k → ℕ)
    (x₀ y₀ x₁ y₁ : Fin k → R) : Matrix (Fin k) (Fin k) R :=
  fun i j ↦ x₀ j ^ r i * x₁ j ^ (H - r i) * y₀ j ^ s i * y₁ j ^ (J - s i)

theorem coefficient_evaluation (G : ℤ[X][X]) (u v : R) :
    (G.map (Polynomial.mapRingHom (Int.castRingHom R))).evalEval u v = evaluate u v G := by
  have he : (Polynomial.evalEvalRingHom u v).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom R))) = evaluate u v := by
    ext <;> simp [evaluate]
  exact RingHom.congr_fun he G

theorem curve_det_zero (p : R) (k : ℕ) (hp : p ^ (k * (k - 1) / 2) = 0)
    (G : ℤ[X][X]) (a b : R) (hG : evaluate a b G ∈ Ideal.span {p})
    (hder : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) (evaluate a b G.derivative)))
    (H J : ℕ) (r s : Fin k → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (x₀ y₀ : Fin k → R) (X Y : Fin k → Rˣ)
    (hx : ∀ j, p ∣ x₀ j * (↑(X j)⁻¹ : R) - a)
    (hy : ∀ j, p ∣ y₀ j * (↑(Y j)⁻¹ : R) - b)
    (hcurve : ∀ j, value G ![x₀ j, (X j : R)] ![y₀ j, (Y j : R)] = 0) :
    (monomialMatrix H J r s x₀ y₀ (fun j ↦ (X j : R)) (fun j ↦ (Y j : R))).det = 0 := by
  let u : Fin k → R := fun j ↦ x₀ j * (↑(X j)⁻¹ : R)
  let v : Fin k → R := fun j ↦ y₀ j * (↑(Y j)⁻¹ : R)
  let Q := G.map (Polynomial.mapRingHom (Int.castRingHom R))
  have hQ : Q.evalEval a b ∈ Ideal.span {p} := by
    simpa only [Q, coefficient_evaluation] using hG
  have hQder : IsUnit (Ideal.Quotient.mk (Ideal.span {p}) (Q.derivative.evalEval a b)) := by
    simpa only [Q, Polynomial.derivative_map, coefficient_evaluation] using hder
  have hroots (j : Fin k) : Q.evalEval (u j) (v j) = 0 := by
    rw [show Q = G.map (Polynomial.mapRingHom (Int.castRingHom R)) from rfl, coefficient_evaluation]
    exact (ProjectiveUnitCharts.zero_iff G (x₀ j) (y₀ j) (X j) (Y j)).mp (hcurve j)
  let F : Fin k → R[X][X] := fun i ↦
    Polynomial.C ((Polynomial.X : R[X]) ^ r i) * (Polynomial.X : R[X][X]) ^ s i
  have hnorm : Matrix.det (fun i j ↦ u j ^ r i * v j ^ s i) = 0 := by
    have h := SmoothCurveDeterminant.smooth_curve_det_zero p k hp Q a b hQ hQder u v hx hy hroots F
    simpa [F, Polynomial.evalEval] using h
  let d : Fin k → R := fun j ↦ (X j : R) ^ H * (Y j : R) ^ J
  have he : monomialMatrix H J r s x₀ y₀ (fun j ↦ (X j : R)) (fun j ↦ (Y j : R)) =
      Matrix.of (fun i j ↦ u j ^ r i * v j ^ s i) * Matrix.diagonal d := by
    ext i j
    rw [Matrix.mul_diagonal]
    change x₀ j ^ r i * (X j : R) ^ (H - r i) * y₀ j ^ s i * (Y j : R) ^ (J - s i) =
      (u j ^ r i * v j ^ s i) * d j
    dsimp only [u, v, d]
    calc
      _ = ((x₀ j * (↑(X j)⁻¹ : R)) ^ r i * (X j : R) ^ H) *
          ((y₀ j * (↑(Y j)⁻¹ : R)) ^ s i * (Y j : R) ^ J) := by
        rw [clear_unit_power _ _ _ _ (hr i), clear_unit_power _ _ _ _ (hs i)]
        ring
      _ = _ := by ring
  have hnorm' : (Matrix.of (fun i j ↦ u j ^ r i * v j ^ s i)).det = 0 := by
    change Matrix.det (fun i j ↦ u j ^ r i * v j ^ s i) = 0
    exact hnorm
  rw [he, Matrix.det_mul, hnorm', zero_mul]

theorem integer_smooth_dvd (p k : ℕ) (hp : p.Prime) (G : ℤ[X][X]) (a b : ℤ)
    (hG : (p : ℤ) ∣ G.evalEval a b) (hder : ¬(p : ℤ) ∣ G.derivative.evalEval a b)
    (H J : ℕ) (r s : Fin k → ℕ) (hr : ∀ i, r i ≤ H) (hs : ∀ i, s i ≤ J)
    (x y : Fin k → Fin 2 → ℤ) (hdenX : ∀ j, ¬(p : ℤ) ∣ x j 1) (hdenY : ∀ j, ¬(p : ℤ) ∣ y j 1)
    (hx : ∀ j, (p : ℤ) ∣ x j 0 - a * x j 1) (hy : ∀ j, (p : ℤ) ∣ y j 0 - b * y j 1)
    (hcurve : ∀ j, MvPolynomial.eval₂ (MvPolynomial.eval (y j)) (x j)
      (PaperP1.IntegerFactorProjectiveCurve.projective G) = 0) :
    (p : ℤ) ^ (k * (k - 1) / 2) ∣
      (monomialMatrix H J r s (fun j ↦ x j 0) (fun j ↦ y j 0)
        (fun j ↦ x j 1) (fun j ↦ y j 1)).det := by
  classical
  let n := k * (k - 1) / 2
  let R₀ := ZMod (p ^ n)
  let φ : ℤ →+* R₀ := Int.castRingHom R₀
  have huX (j : Fin k) : IsUnit (φ (x j 1)) :=
    SmoothIntegerCongruenceBranch.unit_mod_prime_power p n hp _ (hdenX j)
  have huY (j : Fin k) : IsUnit (φ (y j 1)) :=
    SmoothIntegerCongruenceBranch.unit_mod_prime_power p n hp _ (hdenY j)
  choose X hX using huX
  choose Y hY using huY
  have hp0 : (p : R₀) ^ (k * (k - 1) / 2) = 0 := by
    rw [← Nat.cast_pow]
    exact ZMod.natCast_self _
  have hmem (z : ℤ) (hz : (p : ℤ) ∣ z) : φ z ∈ Ideal.span {(p : R₀)} := by
    apply Ideal.mem_span_singleton.mpr
    simpa only [map_natCast] using map_dvd φ hz
  have hbase : evaluate (φ a) (φ b) G ∈ Ideal.span {(p : R₀)} := by
    change evaluate (a : R₀) (b : R₀) G ∈ Ideal.span {(p : R₀)}
    rw [PaperP1.BivariateEvaluation.integer_evaluation]
    exact hmem _ hG
  have hdu : IsUnit (Ideal.Quotient.mk (Ideal.span {(p : R₀)})
      (evaluate (φ a) (φ b) G.derivative)) := by
    have hu : IsUnit (evaluate (φ a) (φ b) G.derivative) := by
      change IsUnit (evaluate (a : R₀) (b : R₀) G.derivative)
      rw [PaperP1.BivariateEvaluation.integer_evaluation]
      exact SmoothIntegerCongruenceBranch.unit_mod_prime_power p n hp _ hder
    exact hu.map _
  have hxR (j : Fin k) : (p : R₀) ∣ φ (x j 0) * (↑(X j)⁻¹ : R₀) - φ a := by
    have hd : (p : R₀) ∣ φ (x j 0) - φ a * (X j : R₀) := by
      rw [hX j]
      simpa only [map_sub, map_mul, map_natCast] using map_dvd φ (hx j)
    have he : (φ (x j 0) - φ a * (X j : R₀)) * (↑(X j)⁻¹ : R₀) =
        φ (x j 0) * (↑(X j)⁻¹ : R₀) - φ a := by
      rw [sub_mul, mul_assoc]
      simp
    rw [← he]
    exact dvd_mul_of_dvd_left hd _
  have hyR (j : Fin k) : (p : R₀) ∣ φ (y j 0) * (↑(Y j)⁻¹ : R₀) - φ b := by
    have hd : (p : R₀) ∣ φ (y j 0) - φ b * (Y j : R₀) := by
      rw [hY j]
      simpa only [map_sub, map_mul, map_natCast] using map_dvd φ (hy j)
    have he : (φ (y j 0) - φ b * (Y j : R₀)) * (↑(Y j)⁻¹ : R₀) =
        φ (y j 0) * (↑(Y j)⁻¹ : R₀) - φ b := by
      rw [sub_mul, mul_assoc]
      simp
    rw [← he]
    exact dvd_mul_of_dvd_left hd _
  have hcurveR (j : Fin k) : value G ![φ (x j 0), (X j : R₀)] ![φ (y j 0), (Y j : R₀)] = 0 := by
    have heX : ![φ (x j 0), (X j : R₀)] = (fun i ↦ φ (x j i)) := by
      funext i
      fin_cases i
      · rfl
      · exact hX j
    have heY : ![φ (y j 0), (Y j : R₀)] = (fun i ↦ φ (y j i)) := by
      funext i
      fin_cases i
      · rfl
      · exact hY j
    rw [heX, heY]
    change value G (fun i ↦ (x j i : R₀)) (fun i ↦ (y j i : R₀)) = 0
    rw [ProjectiveUnitCharts.integer_cast, hcurve j, Int.cast_zero]
  have hdet := curve_det_zero (p : R₀) k hp0 G (φ a) (φ b) hbase hdu H J r s hr hs
    (fun j ↦ φ (x j 0)) (fun j ↦ φ (y j 0)) X Y hxR hyR hcurveR
  let A : Matrix (Fin k) (Fin k) ℤ :=
    monomialMatrix H J r s (fun j ↦ x j 0) (fun j ↦ y j 0) (fun j ↦ x j 1) (fun j ↦ y j 1)
  have hmap : φ.mapMatrix A = monomialMatrix H J r s (fun j ↦ φ (x j 0))
      (fun j ↦ φ (y j 0)) (fun j ↦ (X j : R₀)) (fun j ↦ (Y j : R₀)) := by
    ext i j
    change φ (x j 0 ^ r i * x j 1 ^ (H - r i) * y j 0 ^ s i * y j 1 ^ (J - s i)) =
      φ (x j 0) ^ r i * (X j : R₀) ^ (H - r i) * φ (y j 0) ^ s i * (Y j : R₀) ^ (J - s i)
    simp only [map_mul, map_pow, hX j, hY j]
  have hz : φ A.det = 0 := by
    rw [φ.map_det, hmap]
    exact hdet
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd A.det (p ^ n)).mp hz
  simpa only [Nat.cast_pow] using hd

end PaperP1.ProjectiveSmoothDeterminant
