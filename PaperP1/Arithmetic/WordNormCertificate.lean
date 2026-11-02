module

public import PaperP1.Algebra.BiquadraticNormGenerators
public import PaperP1.Arithmetic.BiquadraticWordNorm

/-! # An honest degree-four field norm certificate for the literal integer word polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WordNormCertificate

open Finset Polynomial PaperP1.BiquadraticNormModel PaperP1.BivariateWordSquares
  PaperP1.BiquadraticWordNorm PaperP1.FormalWordPolynomials PaperP1.BiquadraticSourceNorm
open scoped symmDiff

abbrev Model (I J K L : Finset ℤ) := Second FunctionField (wordFunction I J) (wordFunction K L)

def baseMap (I J K L : Finset ℤ) : FunctionField →+* Model I J K L :=
  BiquadraticNormGenerators.base (wordFunction I J) (wordFunction K L)

def rootOne (I J K L : Finset ℤ) : Model I J K L :=
  BiquadraticNormGenerators.firstRoot (wordFunction I J) (wordFunction K L)

def rootTwo (I J K L : Finset ℤ) : Model I J K L :=
  BiquadraticNormGenerators.secondRoot (wordFunction I J) (wordFunction K L)

def rootThree (I J K L : Finset ℤ) : Model I J K L :=
  BiquadraticNormGenerators.thirdRoot (wordFunction I J) (wordFunction K L) (wordFunction (I ∩ K) (J ∩ L))

def element (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) : Model I J K L :=
  auxiliary (wordFunction I J) (wordFunction K L) (embedding (A 0)) (embedding (A 1)) (embedding (A 2))
    (embedding (A 3) / wordFunction (I ∩ K) (J ∩ L))

theorem model_isField (I J K L : Finset ℤ) (hind : Independent I J K L) : IsField (Model I J K L) :=
  tower_isField _ _ (wordFunction_not_square I J hind.1) (wordFunction_not_square K L hind.2.1)
    (product_not_square I J K L hind.2.2)

theorem model_finrank (I J K L : Finset ℤ) (hind : Independent I J K L) :
    Module.finrank FunctionField (Model I J K L) = 4 :=
  tower_finrank _ _ (wordFunction_not_square I J hind.1)

theorem norm_identity (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) :
    embedding (normPolynomial I J K L A) = Algebra.norm FunctionField (element I J K L A) := by
  have hG := wordFunction_ne_zero (I ∩ K) (J ∩ L)
  have h₃ := (wordFunction_overlap I J K L).symm
  have hh : wordFunction (K \ I) (L \ J) * wordFunction (I ∩ K) (J ∩ L) = wordFunction K L := by
    have hp := congrArg embedding (word_remove_overlap ℤ I J K L)
    simpa only [map_mul, embedding_word, mul_comm] using hp
  rw [normPolynomial, map_sourceNorm]
  simp only [embedding_word]
  exact (source_norm_formula _ _ _ _ _ _ _ _ _ hG h₃ hh).symm

theorem element_ne_zero (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) (hA : ∃ χ, A χ ≠ 0) :
    element I J K L A ≠ 0 := by
  intro hzero
  have h₀ := congrArg (fun z : Model I J K L ↦ z.re.re) hzero
  have h₁ := congrArg (fun z : Model I J K L ↦ z.re.im) hzero
  have h₂ := congrArg (fun z : Model I J K L ↦ z.im.re) hzero
  have h₃ := congrArg (fun z : Model I J K L ↦ z.im.im) hzero
  change embedding (A 0) = 0 at h₀
  change embedding (A 1) = 0 at h₁
  change embedding (A 2) = 0 at h₂
  change embedding (A 3) / wordFunction (I ∩ K) (J ∩ L) = 0 at h₃
  have h₃' : embedding (A 3) = 0 := (div_eq_zero_iff.mp h₃).resolve_right (wordFunction_ne_zero _ _)
  obtain ⟨χ, hχ⟩ := hA
  apply hχ
  apply embedding_injective
  rw [map_zero]
  fin_cases χ <;> assumption

structure Certificate (I J K L : Finset ℤ) (A : Fin 4 → ℤ[X][X]) (R : ℤ[X][X]) : Prop where
  isField : IsField (Model I J K L)
  degreeFour : Module.finrank FunctionField (Model I J K L) = 4
  generated : Algebra.adjoin FunctionField ({rootOne I J K L, rootTwo I J K L} : Set (Model I J K L)) = ⊤
  nonzero : element I J K L A ≠ 0
  normIdentity : embedding R = Algebra.norm FunctionField (element I J K L A)
  expansion : element I J K L A = baseMap I J K L (embedding (A 0)) +
    baseMap I J K L (embedding (A 1)) * rootOne I J K L +
    baseMap I J K L (embedding (A 2)) * rootTwo I J K L +
    baseMap I J K L (embedding (A 3)) * rootThree I J K L
  firstSquare : rootOne I J K L ^ 2 = baseMap I J K L (wordFunction I J)
  secondSquare : rootTwo I J K L ^ 2 = baseMap I J K L (wordFunction K L)
  thirdSquare : rootThree I J K L ^ 2 = baseMap I J K L (wordFunction (I ∆ K) (J ∆ L))
  overlap : baseMap I J K L (wordFunction (I ∩ K) (J ∩ L)) * rootThree I J K L = rootOne I J K L * rootTwo I J K L

theorem certificate (I J K L : Finset ℤ) (hind : Independent I J K L)
    (A : Fin 4 → ℤ[X][X]) (hA : ∃ χ, A χ ≠ 0) : Certificate I J K L A (normPolynomial I J K L A) := by
  refine ⟨model_isField I J K L hind, model_finrank I J K L hind, BiquadraticNormGenerators.generators_top _ _, element_ne_zero I J K L A hA,
    norm_identity I J K L A, ?_, ?_, ?_, ?_, ?_⟩
  · exact BiquadraticNormGenerators.auxiliary_expansion _ _ _ _ _ _ _
  · exact BiquadraticNormGenerators.first_square _ _
  · exact BiquadraticNormGenerators.second_square _ _
  · exact BiquadraticNormGenerators.third_square _ _ _ _ (wordFunction_ne_zero _ _) (wordFunction_overlap I J K L).symm
  · exact BiquadraticNormGenerators.overlap_relation _ _ _ (wordFunction_ne_zero _ _)

end PaperP1.WordNormCertificate
