module

public import PaperP1.Diophantine.ReflectedResultants

/-! # Projective common-factor criteria for a nonzero homogeneous resultant -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ProjectiveResultants

open Polynomial

variable {K : Type*} [Field K]

theorem homogenize_raise (f : K[X]) {m n : ℕ} (hf : f.natDegree ≤ m) (hmn : m ≤ n) :
    f.homogenize n = f.homogenize m * MvPolynomial.X 1 ^ (n - m) := by
  apply Polynomial.homogenize_eq_of_isHomogeneous
  · simpa only [one_mul, Nat.add_sub_of_le hmn] using
      (Polynomial.isHomogeneous_homogenize f (n := m)).mul
        ((MvPolynomial.isHomogeneous_X (R := K) 1).pow (n - m))
  · simp [hf]

theorem native_homogenize_dvd (f : K[X]) {d : ℕ} (hf : f.natDegree ≤ d) :
    f.homogenize f.natDegree ∣ f.homogenize d := by
  rw [homogenize_raise f le_rfl hf]
  exact dvd_mul_right _ _

theorem coprime_of_homogeneous_relprime (f g : K[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hcop : IsRelPrime (f.homogenize d) (g.homogenize d)) : IsCoprime f g := by
  apply IsRelPrime.isCoprime
  intro p hpf hpg
  have hu := hcop
    ((Polynomial.homogenize_dvd hpf).trans (native_homogenize_dvd f hf))
    ((Polynomial.homogenize_dvd hpg).trans (native_homogenize_dvd g hg))
  simpa using hu.map (MvPolynomial.aeval (![Polynomial.X, 1] : Fin 2 → K[X])).toRingHom

theorem full_degree_of_homogeneous_relprime (f g : K[X]) (d : ℕ)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hcop : IsRelPrime (f.homogenize d) (g.homogenize d)) :
    f.natDegree = d ∨ g.natDegree = d := by
  by_contra hfull
  push Not at hfull
  have hfd : 0 < d - f.natDegree := by omega
  have hgd : 0 < d - g.natDegree := by omega
  have hleft : MvPolynomial.X (1 : Fin 2) ∣ f.homogenize d := by
    rw [homogenize_raise f le_rfl hf]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ hfd.ne') _
  have hright : MvPolynomial.X (1 : Fin 2) ∣ g.homogenize d := by
    rw [homogenize_raise g le_rfl hg]
    exact dvd_mul_of_dvd_right (dvd_pow_self _ hgd.ne') _
  have hu := (hcop hleft hright).map (MvPolynomial.eval (fun _ ↦ (0 : K)))
  exact (show (0 : K) ≠ 0 by simpa only [MvPolynomial.eval_X] using hu.ne_zero) rfl

theorem resultant_ne_zero_of_homogeneous_relprime (f g : K[X]) (d : ℕ) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hg : g.natDegree ≤ d)
    (hcop : IsRelPrime (f.homogenize d) (g.homogenize d)) : f.resultant g d d ≠ 0 :=
  PaperP1.ResultantDivisibility.padded_resultant_ne_zero f g d hd hf hg
    (full_degree_of_homogeneous_relprime f g d hf hg hcop)
    (coprime_of_homogeneous_relprime f g d hf hg hcop)

theorem constant_divisor_isUnit_of_irreducible {R ι : Type*} [CommRing R] [IsDomain R]
    {P : MvPolynomial ι R} (hP : Irreducible P)
    (hzero : MvPolynomial.eval (fun _ ↦ (0 : R)) P = 0) {r : R}
    (hr : MvPolynomial.C r ∣ P) : IsUnit r := by
  obtain ⟨Q, hQ⟩ := hr
  rcases hP.isUnit_or_isUnit hQ with hc | hunit
  · simpa using hc.map (MvPolynomial.eval (fun _ ↦ (0 : R)))
  · have heq := congrArg (MvPolynomial.eval (fun _ ↦ (0 : R))) hQ
    simp only [hzero, map_mul, MvPolynomial.eval_C] at heq
    have hr0 : r = 0 := (mul_eq_zero.mp heq.symm).resolve_right
      (hunit.map (MvPolynomial.eval (fun _ ↦ (0 : R)))).ne_zero
    subst r
    simp only [map_zero, zero_mul] at hQ
    exact False.elim (hP.ne_zero hQ)

theorem coefficients_relprime_of_irreducible {R : Type*} [CommRing R] [IsDomain R]
    (F G : R)
    (hP : Irreducible (MvPolynomial.C F * MvPolynomial.X (0 : Fin 2) +
      MvPolynomial.C G * MvPolynomial.X 1)) : IsRelPrime F G := by
  intro r hrF hrG
  apply constant_divisor_isUnit_of_irreducible hP (by simp)
  apply dvd_add
  · exact dvd_mul_of_dvd_left (map_dvd MvPolynomial.C hrF) _
  · exact dvd_mul_of_dvd_left (map_dvd MvPolynomial.C hrG) _

theorem linear_coefficient_left {R : Type*} [CommRing R] (F G : R) :
    (MvPolynomial.C F * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C G * MvPolynomial.X 1).coeff
      (Finsupp.single 0 1) = F := by
  have hne : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 0 1 := by
    intro heq
    have h := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) heq
    simp at h
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, hne]

theorem linear_coefficient_right {R : Type*} [CommRing R] (F G : R) :
    (MvPolynomial.C F * MvPolynomial.X (0 : Fin 2) + MvPolynomial.C G * MvPolynomial.X 1).coeff
      (Finsupp.single 1 1) = G := by
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro heq
    have h := congrArg (fun m : Fin 2 →₀ ℕ ↦ m 0) heq
    simp at h
  simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, hne]

end PaperP1.ProjectiveResultants
