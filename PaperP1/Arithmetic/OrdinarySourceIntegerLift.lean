module

public import PaperP1.Arithmetic.SourceIntegerPoints
public import Mathlib.Tactic.FinCases

/-! # The actual normalized ordinary-to-source integer lift is injective and has exact height H^D -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySourceIntegerLift

open MvPolynomial SourceProjectiveEmbedding OrdinaryIntegerPoints

variable {ι : Type}

def point (D : ℕ) (v : Point ι) : GeneratorIndex ℚ ι D → ℤ :=
  SourceIntegerLift.point D (v (Sum.inl 1)) (v (Sum.inl 0)) (fun i ↦ v (Sum.inr i))

theorem ordinary_reconstruct (v : Point ι) (hZ : v (Sum.inl 2) = 1) :
    OrdinaryIntegerPoints.lift (v (Sum.inl 1)) (v (Sum.inl 0)) (fun i ↦ v (Sum.inr i)) = v := by
  funext i
  cases i with
  | inl j => fin_cases j <;> simp [OrdinaryIntegerPoints.lift, hZ]
  | inr i => rfl

def recover (D : ℕ) (hD : 0 < D) (v : GeneratorIndex ℚ ι D → ℤ) : Point ι :=
  OrdinaryIntegerPoints.lift (SourceIntegerPoints.host D hD v).1 (SourceIntegerPoints.host D hD v).2
    (fun i ↦ v (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D (Sum.inr i)))

theorem recover_point (D : ℕ) (hD : 0 < D) (v : Point ι) (hZ : v (Sum.inl 2) = 1) :
    recover D hD (point D v) = v := by
  simp only [recover, point, SourceIntegerPoints.host_point, SourceIntegerLift.point_radical]
  exact ordinary_reconstruct v hZ

theorem point_injOn (D : ℕ) (hD : 0 < D) : Set.InjOn (point (ι := ι) D) {v | v (Sum.inl 2) = 1} := by
  intro v hv w hw he
  calc
    v = recover D hD (point D v) := (recover_point D hD v hv).symm
    _ = recover D hD (point D w) := congrArg (recover D hD) he
    _ = w := recover_point D hD w hw

theorem coordinates_height (D H : ℕ) (hD : 0 < D) (hH : 1 ≤ H) (v : Point ι)
    (hv : ∀ i, |v i| ≤ (H : ℤ)) : ∀ g, |point D v g| ≤ ((H ^ D : ℕ) : ℤ) := by
  have hnat (i : Fin 3 ⊕ ι) : (v i).natAbs ≤ H := by
    have hh : ((v i).natAbs : ℤ) ≤ (H : ℤ) := by simpa only [Int.natCast_natAbs] using hv i
    exact_mod_cast hh
  have hpow : H ≤ H ^ D := by
    simpa only [pow_one] using (Nat.pow_le_pow_right hH hD : H ^ 1 ≤ H ^ D)
  intro g
  obtain ⟨t, rfl⟩ := (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D).surjective g
  have hg : (point D v (SplitWeightedGeneratorIndex.indexEquiv ℚ ι D t)).natAbs ≤ H ^ D := by
    cases t with
    | inl e =>
      rw [point, SourceIntegerLift.point_base, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow]
      have he : e.val 1 + e.val 0 ≤ D := by
        have hh := e.property
        rw [Finsupp.degree_eq_sum, Fin.sum_univ_three] at hh
        omega
      calc
        (v (Sum.inl 1)).natAbs ^ e.val 1 * (v (Sum.inl 0)).natAbs ^ e.val 0 ≤ H ^ e.val 1 * H ^ e.val 0 :=
          Nat.mul_le_mul (Nat.pow_le_pow_left (hnat _) _) (Nat.pow_le_pow_left (hnat _) _)
        _ = H ^ (e.val 1 + e.val 0) := (pow_add _ _ _).symm
        _ ≤ H ^ D := Nat.pow_le_pow_right hH he
    | inr i =>
      rw [point, SourceIntegerLift.point_radical]
      exact (hnat (Sum.inr i)).trans hpow
  have hh := (Nat.cast_le (α := ℤ)).mpr hg
  simpa only [Int.natCast_natAbs] using hh

theorem point_mem_box [Fintype ι] [DecidableEq ι] (D H : ℕ) (hD : 0 < D) (hH : 1 ≤ H)
    (v : Point ι) (hv : v ∈ OrdinaryIntegerPoints.box H) : point D v ∈ SourceIntegerPoints.box D (H ^ D) := by
  apply (SourceIntegerPoints.mem_box D (H ^ D) _).mpr
  exact ⟨coordinates_height D H hD hH v ((OrdinaryIntegerPoints.mem_box H v).mp hv).1,
    SourceIntegerPoints.point_normalizer D _ _ _⟩

end PaperP1.OrdinarySourceIntegerLift
