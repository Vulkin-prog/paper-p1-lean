module

public import PaperP1.Analysis.SurfaceAuxiliaryDegreeChoice
public import PaperP1.Analysis.P3PrimeMassProxyComparison
public import PaperP1.Algebra.P3GlobalAuxiliaryOfPrimeMass

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3UniformSmoothAuxiliary

open MvPolynomial Finset
open scoped Classical

theorem uniform_degree (d : ℕ) (hd : 0 < d) (D β : ℝ) (hD : 0 < D) (hβ : 0 < β)
    (hmargin : Real.sqrt (D / (d : ℝ)) < β) (T₀ c₀ T₁ c₁ Kmin : ℕ)
    (hT₀ : 0 < T₀) (hT₁ : 0 < T₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℕ, 1 ≤ H → ∀ A : ℕ, 0 < A → A ≤ T₁ * H ^ c₁ →
      ∀ P : MvPolynomial (Fin 4) ℤ, P ≠ 0 → P.IsHomogeneous d →
        ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P → (∀ m, |P.coeff m| ≤ (A : ℤ)) →
      ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ T₀ * H ^ c₀ →
        (∀ p : ℕ, p.Prime → Kmin ≤ p → ¬(p : ℤ) ∣ z →
          (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2) →
      ∀ U : Finset (Fin 4 → ℤ), (∀ v ∈ U, v 3 = 1) →
        (∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) → (∀ v ∈ U, eval v P = 0) →
        (∀ v ∈ U, ∃ k, eval v (pderiv k P) ≠ 0) →
      ∃ (e : ℕ) (G : MvPolynomial (Fin 4) ℤ), d ≤ e ∧ G.IsHomogeneous e ∧
        ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧
        (∀ v ∈ U, eval v G = 0) ∧ (e : ℝ) ≤ C * (H : ℝ) ^ β := by
  let γ : ℝ := 1 / β
  let r : ℝ := (2 / 3 : ℝ) * c₀ + c₁ + ((d - 1 : ℕ) : ℝ)
  let b : ℝ := (2 / 3 : ℝ) * Real.log (T₀ : ℝ) +
    Real.log ((Fintype.card (P3HomogeneousCoefficientFamily.Index (d - 1)) * (d * T₁) : ℕ) : ℝ)
  have hγ : γ < Real.sqrt ((d : ℝ) / D) :=
    SurfaceAuxiliaryDegreeChoice.reciprocal_margin d hd D β hD hβ hmargin
  obtain ⟨K, hKmin, hKtwo, E₀, hdE, hKE, hEtwo, hgap⟩ :=
    P3PrimeMassProxy.exists_gap_parameters d hd D γ r b hD hγ Kmin
  refine ⟨((E₀ + 2 : ℕ) : ℝ), ?_, ?_⟩
  · exact_mod_cast (show 0 < E₀ + 2 by omega)
  intro H hH A hA hAbound P hP0 hhom hnot hcoef z hz hzbound hclass U hnormal hheight hroots hgrad
  let e := SurfaceAuxiliaryDegreeChoice.degree E₀ H β
  have heE : E₀ ≤ e := SurfaceAuxiliaryDegreeChoice.minimum_le E₀ H β
  have hed : d ≤ e := hdE.trans heE
  have heK : K ≤ e := hKE.trans heE
  have he1 : 1 ≤ e := by omega
  have hlog : Real.log (H : ℝ) ≤ γ * Real.log (e : ℝ) :=
    SurfaceAuxiliaryDegreeChoice.log_height_bound E₀ H β hβ hH
  let S := CertificatePrimeWindow.primes K e z
  have hprimes : ∀ p ∈ S, p.Prime := fun p hp ↦ (CertificatePrimeWindow.mem_primes K e p z).mp hp |>.1
  have hlarge : ∀ p ∈ S, (K : ℝ) ≤ p := by
    intro p hp
    have hh := ((CertificatePrimeWindow.mem_primes K e p z).mp hp).2.1
    exact_mod_cast hh.le
  have hclasses : ∀ p ∈ S, (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2 := by
    intro p hp
    have hh := (CertificatePrimeWindow.mem_primes K e p z).mp hp
    exact hclass p hh.1 (hKmin.trans hh.2.1.le) hh.2.2.2
  have hcompare := P3PrimeMassProxyComparison.value_le_lowerBound d e A H T₀ c₀ T₁ c₁ K hd hA hH
    hT₀ hT₁ (by omega) he1 heK z hz hzbound hAbound D γ hlog
  have hstrict := hgap e heE
  have hweight := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (P3StandardMonomialParameters.weight d e))
  have hleft : Real.log ((P3StandardMonomialParameters.size d e).factorial : ℝ) +
      (P3StandardMonomialParameters.weight d e : ℝ) * Real.log (H : ℝ) ≤
      Real.log ((P3StandardMonomialParameters.size d e).factorial : ℝ) +
        γ * (P3StandardMonomialParameters.weight d e : ℝ) * Real.log (e : ℝ) := by
    nlinarith only [hweight]
  have hnumeric := hleft.trans_lt (hstrict.trans_le hcompare)
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  obtain ⟨G, hGe, hGnot, hGzero⟩ := P3GlobalAuxiliaryOfPrimeMass.exists_auxiliary d e A H hd hed hA hH
    P hP0 hhom hnot hcoef U hnormal hheight hroots hgrad D K hD hKR S hprimes hlarge hclasses hnumeric
  exact ⟨e, G, hed, hGe, hGnot, hGzero, SurfaceAuxiliaryDegreeChoice.degree_bound E₀ H β hβ.le hH⟩

end PaperP1.P3UniformSmoothAuxiliary
