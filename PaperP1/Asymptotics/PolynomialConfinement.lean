module

public import PaperP1.Asymptotics.DivisorAuxiliaryPolynomialUniform
public import PaperP1.Asymptotics.OffsetLineDivisorCountUniform
public import PaperP1.Asymptotics.BoundedPlaneCurveCount
public import PaperP1.Arithmetic.PolynomialOffsetPopulation
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Complete unconditional indexed common-divisor confinement

The auxiliary polynomial, factor cover, line and multiplicity bounds and the
fixed-degree nonlinear point count are all supplied by internal proofs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialConfinement

universe u

open Finset Polynomial PaperP1.BivariateFactorDegree

def afterExactAlignments {ι : Type*} (S : Finset ι) (s t : ι → ℤ) (x y : ℤ) : Finset ι := by
  classical
  exact S.filter fun i ↦ ∀ j ∈ S, (s i, t i) = (s j, t j) ∨
    (x + s i) * (y + t j) ≠ (x + s j) * (y + t i)

theorem afterExactAlignments_no_exact {ι : Type*} (S : Finset ι) (s t : ι → ℤ) (x y : ℤ) :
    ∀ i ∈ afterExactAlignments S s t x y, ∀ j ∈ afterExactAlignments S s t x y,
      (s i, t i) ≠ (s j, t j) → (x + s i) * (y + t j) ≠ (x + s j) * (y + t i) := by
  classical
  intro i hi j hj hne
  rcases (mem_filter.mp hi).2 j (mem_filter.mp hj).1 with he | he
  · exact False.elim (hne he)
  · exact he

theorem companion_T8_1_power (C τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ) (A K : ℕ) (hA : 1 ≤ A) (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) (S : Finset ι) (s t : ι → ℤ) (g : ι → ℕ),
      ∀ x y : ℤ, (N : ℤ) ≤ (A : ℤ) * x → x.natAbs ≤ A * N → y.natAbs ≤ A * N →
      (∀ i ∈ S, (s i).natAbs ≤ K * (L + 1)) → (∀ i ∈ S, (t i).natAbs ≤ K * (L + 1)) →
      (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)) →
      (∀ i ∈ S, (g i : ℤ) ∣ x + s i) → (∀ i ∈ S, (g i : ℤ) ∣ y + t i) →
      (∀ i ∈ S, (N : ℝ) ^ τ ≤ (g i : ℝ)) →
      (∀ i ∈ S, ∀ j ∈ S, (s i, t i) ≠ (s j, t j) →
        (x + s i) * (y + t j) ≠ (x + s j) * (y + t i)) →
      (S.card : ℝ) ≤ M * ((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) := by
  classical
  obtain ⟨d, hd, NP, _hNP, hp⟩ := DivisorAuxiliaryPolynomialUniform.uniform_polynomial C τ hτ A K hA hK
  obtain ⟨NL, _hNL, hl⟩ := OffsetLineDivisorCountUniform.uniform_lines C τ hτ A K hA
  obtain ⟨B₀, hB₀, hb⟩ := BoundedPlaneCurveCount.uniform_bound (2 * d) K hK δ hδ
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  let M : ℝ := ((2 * d : ℕ) : ℝ) * (3 / τ)
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨M, hM, max 2 (max NP (max NL NG)), by omega, ?_⟩
  intro N hN L hband ι S s t g x y hxlo hx hy hs ht hcop hdivs hdivt hlarge hno
  have hcopS : Pairwise (fun i j : S ↦ (g i).Coprime (g j)) := by
    intro i j hij
    exact hcop i.property j.property (fun he ↦ hij (Subtype.ext he))
  obtain ⟨P, hP, houter, hinner, _htotal, hz⟩ := hp N (by omega) L hband S x y hx hy
    (fun i : S ↦ s i) (fun i : S ↦ t i) (fun i : S ↦ g i) hcopS
    (fun i ↦ hs i i.property) (fun i ↦ ht i i.property)
    (fun i ↦ hdivs i i.property) (fun i ↦ hdivt i i.property) (fun i ↦ hlarge i i.property)
  have hwidth : B₀ ≤ L + 1 := (hg N (by omega) L hband).2.1
  have hlines (T : Finset ι) (hTS : T ⊆ S)
      (hcol : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T,
        (s j - s i) * (t k - t i) = (t j - t i) * (s k - s i)) :
      (T.card : ℝ) ≤ 3 / τ := by
    exact hl N (by omega) L hband ι T s t g x y hxlo hx hy
      (fun i hi ↦ hs i (hTS hi)) (fun i hi ↦ ht i (hTS hi))
      (fun i hi j hj hij ↦ hcop (hTS hi) (hTS hj) hij)
      (fun i hi ↦ hdivs i (hTS hi)) (fun i hi ↦ hdivt i (hTS hi))
      (fun i hi ↦ hlarge i (hTS hi)) (fun i hi j hj hne ↦ hno i (hTS hi) j (hTS hj) hne) hcol
  have hF : 1 ≤ ((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ L + 1 by omega)) (by linarith)
  exact PolynomialOffsetPopulation.finite_bound S s t P (K * (L + 1)) (2 * d)
    (3 / τ) (((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ)) (by positivity) hF hP
    (rectangle_bound P d houter hinner) hs ht (fun i hi ↦ hz ⟨i, hi⟩) hlines
    (fun Q hirr hdegree hcap ↦ hb (L + 1) (by omega) Q hirr hdegree hcap)

theorem companion_T8_1_little_o (C τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (A K : ℕ) (hA : 1 ≤ A) (hK : 1 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) (S : Finset ι) (s t : ι → ℤ) (g : ι → ℕ),
      ∀ x y : ℤ, (N : ℤ) ≤ (A : ℤ) * x → x.natAbs ≤ A * N → y.natAbs ≤ A * N →
      (∀ i ∈ S, (s i).natAbs ≤ K * (L + 1)) → (∀ i ∈ S, (t i).natAbs ≤ K * (L + 1)) →
      (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)) →
      (∀ i ∈ S, (g i : ℤ) ∣ x + s i) → (∀ i ∈ S, (g i : ℤ) ∣ y + t i) →
      (∀ i ∈ S, (N : ℝ) ^ τ ≤ (g i : ℝ)) →
      (∀ i ∈ S, ∀ j ∈ S, (s i, t i) ≠ (s j, t j) →
        (x + s i) * (y + t j) ≠ (x + s j) * (y + t i)) →
      (S.card : ℝ) ≤ ε * ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨M, _hM, NP, _hNP, hp⟩ := companion_T8_1_power C τ δ hτ hδ A K hA hK
  obtain ⟨B₀, hb⟩ := HalfCountSchedule.factor_absorption (M / ε) (1 / 2 + δ)
    (1 / 2 - δ) (by linarith)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C B₀
  refine ⟨max 2 (max NP NG), by omega, ?_⟩
  intro N hN L hband ι S s t g x y hxlo hx hy hs ht hcop hdivs hdivt hlarge hno
  have hcount := hp N (by omega) L hband ι S s t g x y hxlo hx hy hs ht hcop hdivs hdivt hlarge hno
  have hwidth := (hg N (by omega) L hband).2.1
  have hfactor := hb (L + 1) hwidth
  rw [show (1 / 2 + δ) + (1 / 2 - δ) = (1 : ℝ) by ring, Real.rpow_one] at hfactor
  have hm := mul_le_mul_of_nonneg_left hfactor hε.le
  have he : ε * (M / ε * ((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ)) =
      M * ((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) := by field_simp
  rw [he] at hm
  exact hcount.trans hm

theorem companion_T8_1_after_alignments (C τ δ : ℝ) (hτ : 0 < τ) (hδ : 0 < δ)
    (A K : ℕ) (hA : 1 ≤ A) (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 < M ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (ι : Type u) (S : Finset ι) (s t : ι → ℤ) (g : ι → ℕ),
      ∀ x y : ℤ, (N : ℤ) ≤ (A : ℤ) * x → x.natAbs ≤ A * N → y.natAbs ≤ A * N →
      (∀ i ∈ S, (s i).natAbs ≤ K * (L + 1)) → (∀ i ∈ S, (t i).natAbs ≤ K * (L + 1)) →
      (S : Set ι).Pairwise (fun i j ↦ (g i).Coprime (g j)) →
      (∀ i ∈ S, (g i : ℤ) ∣ x + s i) → (∀ i ∈ S, (g i : ℤ) ∣ y + t i) →
      (∀ i ∈ S, (N : ℝ) ^ τ ≤ (g i : ℝ)) →
      ((afterExactAlignments S s t x y).card : ℝ) ≤ M * ((L + 1 : ℕ) : ℝ) ^ (1 / 2 + δ) := by
  classical
  obtain ⟨M, hM, N₀, hN₀, hp⟩ := companion_T8_1_power C τ δ hτ hδ A K hA hK
  refine ⟨M, hM, N₀, hN₀, ?_⟩
  intro N hN L hband ι S s t g x y hxlo hx hy hs ht hcop hdivs hdivt hlarge
  have hsub : afterExactAlignments S s t x y ⊆ S := filter_subset _ _
  exact hp N hN L hband ι (afterExactAlignments S s t x y) s t g x y hxlo hx hy
    (fun i hi ↦ hs i (hsub hi)) (fun i hi ↦ ht i (hsub hi))
    (fun i hi j hj hij ↦ hcop (hsub hi) (hsub hj) hij)
    (fun i hi ↦ hdivs i (hsub hi)) (fun i hi ↦ hdivt i (hsub hi))
    (fun i hi ↦ hlarge i (hsub hi)) (afterExactAlignments_no_exact S s t x y)

end PaperP1.PolynomialConfinement
