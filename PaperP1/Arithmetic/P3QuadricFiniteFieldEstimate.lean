module

public import PaperP1.Arithmetic.P3FiniteFieldClassEstimate
public import PaperP1.Diophantine.FiniteFieldQuadricLastChartCount
public import PaperP1.Algebra.FieldExtensionPolynomialIrreducibility
public import PaperP1.Arithmetic.P3CertificateFromNoetherForms

/-! # The leading-coefficient-one finite-field geometric input is proved in degree two -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3QuadricFiniteFieldEstimate

open MvPolynomial Finset P3CanonicalSmoothResidues
open scoped Classical

theorem reduced_evaluation (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (r : Fin 3 → Fin p) :
    eval (Fin.snoc (P3CoarseCanonicalClassCount.fieldCoordinates r) 1)
      (map (Int.castRingHom (ZMod p)) P) = ((eval (representative r) P : ℤ) : ZMod p) := by
  have he := IntegerPolynomialReduction.map_evaluation (Int.castRingHom (ZMod p)) (representative r) P
  have hcoords : (fun k ↦ (Int.castRingHom (ZMod p)) (representative r k)) =
      Fin.snoc (P3CoarseCanonicalClassCount.fieldCoordinates r) 1 := by
    funext k
    cases k using Fin.lastCases with
    | last =>
      have hr : representative r (Fin.last 3) = 1 := representative_last r
      rw [hr, Fin.snoc_last, map_one]
    | cast k => simp [representative, P3CoarseCanonicalClassCount.fieldCoordinates]
  rw [hcoords] at he
  exact he.symm

theorem reduced_gradient (p : ℕ) (P : MvPolynomial (Fin 4) ℤ) (c : Class p P) :
    ∃ k : Fin 4, eval (Fin.snoc (P3CoarseCanonicalClassCount.fieldCoordinates c.val) 1)
      (pderiv k (map (Int.castRingHom (ZMod p)) P)) ≠ 0 := by
  obtain ⟨k, hk⟩ := c.property.2
  refine ⟨k, ?_⟩
  rw [pderiv_map, reduced_evaluation]
  intro hz
  exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)

theorem cardinality_bound (p : ℕ) (hp : p.Prime) (P : MvPolynomial (Fin 4) ℤ)
    (hP : P.IsHomogeneous 2) (hirr : Irreducible (map (Int.castRingHom (ZMod p)) P)) :
    Fintype.card (Class p P) ≤ p ^ 2 + 2 * p := by
  let : Fact p.Prime := ⟨hp⟩
  let f : Class p P → Fin 3 → ZMod p := fun c ↦ P3CoarseCanonicalClassCount.fieldCoordinates c.val
  have hf : Function.Injective f :=
    (P3CoarseCanonicalClassCount.fieldCoordinates_injective p).comp Subtype.val_injective
  let S := (univ : Finset (Class p P)).image f
  have hcard : S.card = Fintype.card (Class p P) := by
    dsimp only [S]
    rw [card_image_of_injective _ hf, card_univ]
  have hroot (c : Class p P) :
      eval (Fin.snoc (f c) 1) (map (Int.castRingHom (ZMod p)) P) = 0 := by
    rw [reduced_evaluation]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr c.property.1
  by_cases h : (univ : Finset (Class p P)).Nonempty
  · obtain ⟨c, _hc⟩ := h
    have hb := FiniteFieldQuadricLastChartCount.cardinality_bound
      (map (Int.castRingHom (ZMod p)) P) (hP.map _) hirr (f c) (hroot c)
      (reduced_gradient p P c) S (by
        intro v hv
        obtain ⟨c, _, rfl⟩ := mem_image.mp hv
        exact hroot c)
    rw [hcard, ZMod.card] at hb
    exact hb
  · have hz : (univ : Finset (Class p P)) = ∅ := not_nonempty_iff_eq_empty.mp h
    have hc : Fintype.card (Class p P) = 0 := by rw [← card_univ, hz, card_empty]
    rw [hc]
    exact Nat.zero_le _

theorem uniform_estimate : P3FiniteFieldClassEstimate.UniformEstimate 2 := by
  intro η hη
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / η)
  refine ⟨K, ?_⟩
  intro p hp hlarge P hP hgeom
  let : Fact p.Prime := ⟨hp⟩
  have hi : Irreducible (map (Int.castRingHom (ZMod p)) P) :=
    FieldExtensionPolynomialIrreducibility.irreducible_of_map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) _ hgeom
  have hb : (Fintype.card (Class p P) : ℝ) ≤ (p : ℝ) ^ 2 + 2 * (p : ℝ) := by
    exact_mod_cast cardinality_bound p hp P hP hi
  have hlargeR : (K : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlarge
  have htwo : (2 : ℝ) ≤ (p : ℝ) * η := (div_le_iff₀ hη).mp (hK.le.trans hlargeR)
  have hmul := mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  apply hb.trans
  nlinarith

theorem of_degree_le_two (d : ℕ) (hd : d ≤ 2) : P3FiniteFieldClassEstimate.UniformEstimate d := by
  by_cases h : d ≤ 1
  · exact P3FiniteFieldClassEstimate.of_degree_le_one d h
  · have he : d = 2 := by omega
    rw [he]
    exact uniform_estimate

theorem uniform_auxiliary_of_noether_forms (hforms : P3UniversalNoetherForms.ExistsForms 2) :
    UniformP3AuxiliaryHypersurface.UniformAuxiliary 2 :=
  P3CertificateFromNoetherForms.uniform_auxiliary 2 hforms uniform_estimate

end PaperP1.P3QuadricFiniteFieldEstimate
