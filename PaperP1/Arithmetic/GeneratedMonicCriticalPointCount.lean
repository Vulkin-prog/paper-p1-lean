module

public import PaperP1.Algebra.GeneratedThreeCoordinatePoints
public import PaperP1.Arithmetic.MonicCriticalPointCount

/-! # Actual generated-algebra points killing a literal derivative have the critical-locus count -/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.GeneratedMonicCriticalPointCount
open Polynomial Finset GeneratedThreeCoordinatePoints
open scoped Classical
variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]

theorem exceptional_cardinality [Fintype F] (p : ℕ) [CharP F p]
    (v : Fin 2 → A) (z δ : A) (hgen : Algebra.adjoin F (Set.range (Fin.cons z v)) = ⊤)
    (P : (MvPolynomial (Fin 2) F)[X]) (hmonic : P.Monic) (hP : Irreducible P)
    (hpos : 0 < P.natDegree) (d : ℕ) (hdegree : P.natDegree ≤ d) (hlt : d < p)
    (hcoef : ∀ i, (P.coeff i).totalDegree ≤ d)
    (hequation : P.eval₂ (MvPolynomial.aeval v).toRingHom z = 0)
    (hδ : δ = P.derivative.eval₂ (MvPolynomial.aeval v).toRingHom z) :
    Nat.card {φ : A →ₐ[F] F // φ δ = 0} ≤ 2*d^3*Fintype.card F := by
  let : Finite (A →ₐ[F] F) := points_finite (Fin.cons z v) hgen
  let : Fintype (A →ₐ[F] F) := Fintype.ofFinite _
  let S := (univ : Finset {φ : A →ₐ[F] F // φ δ = 0}).image (fun φ ↦ values v z φ.val)
  have hinj : Function.Injective (fun φ : {φ : A →ₐ[F] F // φ δ = 0} ↦ values v z φ.val) :=
    (values_injective v z hgen).comp Subtype.val_injective
  have hc : S.card = Fintype.card {φ : A →ₐ[F] F // φ δ = 0} := by
    dsimp only [S]
    rw [card_image_of_injective _ hinj, card_univ]
  have hS : ∀ w ∈ S, P.eval₂ (MvPolynomial.eval w.1) w.2 = 0 ∧
      P.derivative.eval₂ (MvPolynomial.eval w.1) w.2 = 0 := by
    intro w hw
    obtain ⟨φ, _, rfl⟩ := mem_image.mp hw
    have hr := congrArg φ.val hequation
    rw [mixed_evaluation v z φ.val P, map_zero] at hr
    have hd : P.derivative.eval₂ (MvPolynomial.eval (fun i ↦ φ.val (v i))) (φ.val z) = 0 := by
      rw [← mixed_evaluation v z φ.val P.derivative, ← hδ]
      exact φ.property
    exact ⟨hr, hd⟩
  calc
    Nat.card {φ : A →ₐ[F] F // φ δ = 0} = Fintype.card {φ : A →ₐ[F] F // φ δ = 0} :=
      Nat.card_eq_fintype_card
    _ = S.card := hc.symm
    _ ≤ _ := PaperP1.MonicCriticalPointCount.critical_points_card_degree_cap
      p P hmonic hP hpos d hdegree hlt hcoef S hS

end PaperP1.GeneratedMonicCriticalPointCount
