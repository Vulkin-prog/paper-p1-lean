module

public import PaperP1.Arithmetic.CurveCoordinateCut
public import PaperP1.Arithmetic.CurveSquareGridBound
public import PaperP1.Arithmetic.CommonCurveTheorem

/-! # The integer-grid lower bound for the actual common curve -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerGridTheorem

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateTotalDegree PaperP1.BivariateHeight
  PaperP1.CurveWordMap PaperP1.CurveIntegerFibres PaperP1.CurveCoordinateCut
  PaperP1.FormalWordPolynomials PaperP1.CommonCurveTheorem

local instance : CommRing ℤ[X][X] := inferInstance
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : AddCommGroup Words := inferInstance
local instance (V : Submodule (ZMod 2) Words) : AddCommGroup V := inferInstance
local instance (V : Submodule (ZMod 2) Words) : Module (ZMod 2) V := V.module

theorem floor_box_iff (B : ℝ) (hB : 0 ≤ B) (u : ℤ) :
    u ∈ offsetBox ⌊B⌋₊ ↔ |(u : ℝ)| ≤ B := by
  constructor
  · intro hu
    have h : |(u : ℝ)| ≤ (⌊B⌋₊ : ℝ) := by
      exact_mod_cast (mem_offsetBox ⌊B⌋₊ u).mp hu
    exact h.trans (Nat.floor_le hB)
  · intro hu
    exact (mem_offsetBox ⌊B⌋₊ u).mpr (TwoWitnessTheorem.floor_offset B hB u hu)

theorem mem_real_grid (C₀ : ℤ[X][X]) (B : ℝ) (hB : 0 ≤ B) (p : ℤ × ℤ) :
    p ∈ integerGrid C₀ ⌊B⌋₊ ↔
      |(p.1 : ℝ)| ≤ B ∧ |(p.2 : ℝ)| ≤ B ∧ C₀.evalEval (-p.1) (-p.2) = 0 := by
  rw [mem_integerGrid, ← mem_offsetBox, ← mem_offsetBox, floor_box_iff B hB, floor_box_iff B hB]

theorem real_rhs_le_truncated (d t D : ℕ) :
    (d : ℝ) * ((t : ℝ) - 1 - 6 * (D : ℝ) ^ 2) ≤ (d * (t - 1 - 6 * D ^ 2) : ℕ) := by
  have hn : t ≤ (t - 1 - 6 * D ^ 2) + 1 + 6 * D ^ 2 := by omega
  have hc : (t : ℝ) ≤ ((t - 1 - 6 * D ^ 2 : ℕ) : ℝ) + 1 + 6 * (D : ℝ) ^ 2 := by
    exact_mod_cast hn
  have hsub : (t : ℝ) - 1 - 6 * (D : ℝ) ^ 2 ≤ ((t - 1 - 6 * D ^ 2 : ℕ) : ℝ) := by linarith
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg d : (0 : ℝ) ≤ d)

theorem certificate_grid_bound (V : Submodule (ZMod 2) Words) [Module.Finite (ZMod 2) V]
    (cert : Certificate V) (B : ℕ)
    (hfirst : Function.Injective (fun w : V ↦ (w : Words).1))
    (hsecond : Function.Injective (fun w : V ↦ (w : Words).2))
    (hboundfirst : ∀ w : V, (w : Words).1.support ⊆ offsetBox B)
    (hboundsecond : ∀ w : V, (w : Words).2.support ⊆ offsetBox B) :
    max (degreeX cert.polynomial) (degreeY cert.polynomial) *
      (Module.finrank (ZMod 2) V - 1 - 6 * totalDegree cert.polynomial ^ 2) ≤
        (integerGrid cert.polynomial B).card := by
  let : Fact (Irreducible cert.polynomial) := ⟨cert.irreducible⟩
  let : AddCommGroup (SquareSpace cert.polynomial cert.degreeX_pos cert.degreeY_pos V) := inferInstance
  let : Module (ZMod 2) (SquareSpace cert.polynomial cert.degreeX_pos cert.degreeY_pos V) :=
    (SquareSpace cert.polynomial cert.degreeX_pos cert.degreeY_pos V).module
  let E := RegularSpace cert.polynomial cert.degreeX_pos cert.degreeY_pos V
  let : AddCommGroup E := inferInstance
  let : Module (ZMod 2) E := (RegularSpace cert.polynomial cert.degreeX_pos cert.degreeY_pos V).module
  let b := Module.finBasis (ZMod 2) E
  let w := inclusion cert.polynomial cert.degreeX_pos cert.degreeY_pos V
  let f : E →ₗ[ZMod 2] (ℤ →₀ ZMod 2) := (LinearMap.fst _ _ _).comp w
  let g : E →ₗ[ZMod 2] (ℤ →₀ ZMod 2) := (LinearMap.snd _ _ _).comp w
  have hf : Function.Injective f := by
    intro a a' h
    apply Subtype.ext
    apply Subtype.ext
    exact hfirst h
  have hg : Function.Injective g := by
    intro a a' h
    apply Subtype.ext
    apply Subtype.ext
    exact hsecond h
  have hgrid := CurveSquareGridBound.basis_grid_bound cert.polynomial cert.degreeX_pos cert.degreeY_pos
    b f g hf hg B (fun i ↦ hboundfirst (b i).val.val) (fun i ↦ hboundsecond (b i).val.val)
    (fun i ↦ literal_square cert.polynomial cert.degreeX_pos cert.degreeY_pos V (b i))
    (fun i ↦ first_regular cert.polynomial cert.degreeX_pos cert.degreeY_pos V (b i))
    (fun i ↦ second_regular cert.polynomial cert.degreeX_pos cert.degreeY_pos V (b i))
  have hdim := dimension_lower cert.polynomial cert.degreeX_pos cert.degreeY_pos V cert.image_rank
  exact (Nat.mul_le_mul_left _ hdim).trans hgrid

theorem basis_support_bounds {ι : Type*} [Fintype ι] (V : Submodule (ZMod 2) Words)
    (b : Module.Basis ι (ZMod 2) V) (I J : ι → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i))) (B : ℕ)
    (hI : ∀ i u, u ∈ I i → |u| ≤ (B : ℤ)) (hJ : ∀ i v, v ∈ J i → |v| ≤ (B : ℤ)) :
    (∀ w : V, (w : Words).1.support ⊆ offsetBox B) ∧
      (∀ w : V, (w : Words).2.support ⊆ offsetBox B) := by
  let f : V →ₗ[ZMod 2] (ℤ →₀ ZMod 2) := (LinearMap.fst _ _ _).comp V.subtype
  let g : V →ₗ[ZMod 2] (ℤ →₀ ZMod 2) := (LinearMap.snd _ _ _).comp V.subtype
  constructor
  · apply FiniteSupportImageRank.support_subset_of_basis (K := ZMod 2) (E := V) b f (offsetBox B)
    intro i
    change ((b i : Words).1).support ⊆ offsetBox B
    rw [hwords, FormalWordEncoding.support_encode]
    exact fun u hu ↦ (mem_offsetBox B u).mpr (hI i u hu)
  · apply FiniteSupportImageRank.support_subset_of_basis (K := ZMod 2) (E := V) b g (offsetBox B)
    intro i
    change ((b i : Words).2).support ⊆ offsetBox B
    rw [hwords, FormalWordEncoding.support_encode]
    exact fun v hv ↦ (mem_offsetBox B v).mpr (hJ i v hv)

theorem article_13_3 {t : ℕ} (ht : 2 ≤ t) (V : Submodule (ZMod 2) Words)
    (b : Module.Basis (Fin t) (ZMod 2) V) (I J : Fin t → Finset ℤ)
    (hwords : ∀ i, (b i : Words) = (encode (I i), encode (J i)))
    (hfirst : Function.Injective (fun w : V ↦ (w : Words).1))
    (hsecond : Function.Injective (fun w : V ↦ (w : Words).2))
    (B q : ℝ) (hq : 1 ≤ q) (hqB : q ≤ B)
    (hevenI : ∀ i, Even (I i).card) (hevenJ : ∀ i, Even (J i).card)
    (hcardI : ∀ i, ((I i).card : ℝ) ≤ 2 * q) (hcardJ : ∀ i, ((J i).card : ℝ) ≤ 2 * q)
    (hI : ∀ i u, u ∈ I i → |(u : ℝ)| ≤ B) (hJ : ∀ i v, v ∈ J i → |(v : ℝ)| ≤ B)
    (N : ℝ) (x y : ℤ) (hx : N ≤ (x : ℝ)) (hy : N ≤ (y : ℝ))
    (hx₂ : (x : ℝ) ≤ 2 * N) (hy₂ : (y : ℝ) ≤ 2 * N)
    (hlarge : (B + 1) ^ (1000000 * q ^ 2) < N)
    (hsquare : ∀ i, IsSquare ((wordOver ℤ (I i) (J i)).evalEval x y)) :
    ∃ cert : Certificate V, cert.polynomial.evalEval x y = 0 ∧
      (totalDegree cert.polynomial : ℝ) ≤ 48 * q ∧
      (height cert.polynomial : ℝ) ≤ (B + 1) ^ (1000000 * q) ∧
      max (degreeX cert.polynomial) (degreeY cert.polynomial) *
        (t - 1 - 6 * totalDegree cert.polynomial ^ 2) ≤ (integerGrid cert.polynomial ⌊B⌋₊).card ∧
      ((max (degreeX cert.polynomial) (degreeY cert.polynomial) : ℕ) : ℝ) *
        ((t : ℝ) - 1 - 6 * (totalDegree cert.polynomial : ℝ) ^ 2) ≤
          ((integerGrid cert.polynomial ⌊B⌋₊).card : ℝ) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_basis b
  have hB : 0 ≤ B := by linarith
  obtain ⟨cert, hpoint, hdegree, hheight⟩ := CommonCurveTheorem.article_13_2 ht V b I J hwords
    B q hq hqB hevenI hevenJ hcardI hcardJ hI hJ N x y hx hy hx₂ hy₂ hlarge hsquare
  obtain ⟨hboundfirst, hboundsecond⟩ := basis_support_bounds V b I J hwords ⌊B⌋₊
    (fun i u hu ↦ TwoWitnessTheorem.floor_offset B hB u (hI i u hu))
    (fun i v hv ↦ TwoWitnessTheorem.floor_offset B hB v (hJ i v hv))
  refine ⟨cert, hpoint, hdegree, hheight, ?_⟩
  have hgrid := certificate_grid_bound V cert ⌊B⌋₊ hfirst hsecond hboundfirst hboundsecond
  have hdim : Module.finrank (ZMod 2) V = t := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  rw [hdim] at hgrid
  refine ⟨hgrid, ?_⟩
  have hcast : ((max (degreeX cert.polynomial) (degreeY cert.polynomial) *
      (t - 1 - 6 * totalDegree cert.polynomial ^ 2) : ℕ) : ℝ) ≤
        ((integerGrid cert.polynomial ⌊B⌋₊).card : ℝ) := by exact_mod_cast hgrid
  exact (real_rhs_le_truncated (max (degreeX cert.polynomial) (degreeY cert.polynomial)) t
    (totalDegree cert.polynomial)).trans hcast

end PaperP1.IntegerGridTheorem
