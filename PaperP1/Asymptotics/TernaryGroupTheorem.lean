module

public import PaperP1.Asymptotics.TernaryPatternBudget

/-! # Companion T1.16 for the source even-map hypotheses and actual tuple counts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryGroupTheorem

open Finset PaperP1.TernaryTopProducts PaperP1.FiniteEvenSquareClasses PaperP1.TernaryBudgetDomain

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

structure SourceAdmissible (N L R D : ℕ) (base : Fin 3 → ℕ)
    (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ) (X : Fin 3 → ℕ) : Prop where
  box : ∀ i, X i ∈ Ico (base i) (base i + D * N)
  cutoff : 1 ≤ H X ∧ H X ≤ D * (L + 1)
  diameter : ∀ i, ∀ n ∈ U X i, ∀ m ∈ U X i, ((n : ℤ) - m).natAbs ≤ H X
  values : ∀ i, ∀ n ∈ U X i, 0 < n ∧ n ≤ D * N ∧ ((n : ℤ) - X i).natAbs ≤ R
  even_injective : ∀ i, Function.Injective (EvenImage.evenMap (K := Arithmetic.F₂) (data (U X i)))
  disjoint : Pairwise (fun i j ↦ Disjoint (space (U X i)) (space (U X j)))

theorem SourceAdmissible.toAdmissible {N L R D : ℕ} {base : Fin 3 → ℕ}
    {U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ} {H : (Fin 3 → ℕ) → ℕ} {X : Fin 3 → ℕ}
    (h : SourceAdmissible N L R D base U H X) : Admissible N L R D base U H X :=
  ⟨h.box, h.cutoff, h.diameter, h.values,
    fun i ↦ FiniteEvenSetRigidity.data_injective_of_evenMap (U X i) (h.even_injective i), h.disjoint⟩

def sourceCentres (N L R D k : ℕ) (base : Fin 3 → ℕ)
    (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ) (T : ℝ) : Finset (Fin 3 → ℕ) := by
  classical
  exact (CRTProductCover.box 3 base (D * N)).filter fun X ↦
    SourceAdmissible N L R D base U H X ∧ T < (topProduct (U X) (H X) k : ℝ)

theorem mem_sourceCentres (N L R D k : ℕ) (base : Fin 3 → ℕ)
    (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : (Fin 3 → ℕ) → ℕ) (T : ℝ) (X : Fin 3 → ℕ) :
    X ∈ sourceCentres N L R D k base U H T ↔
      SourceAdmissible N L R D base U H X ∧ T < (topProduct (U X) (H X) k : ℝ) := by
  classical
  constructor
  · intro hX
    exact (mem_filter.mp hX).2
  · intro hX
    exact mem_filter.mpr ⟨Fintype.mem_piFinset.mpr hX.1.box, hX⟩

theorem bounded_cutoff_patterns (C : ℝ) (D k J : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceAdmissible N L R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, T < (topProduct (U z.1 z.2) (H z.1 z.2) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 / T ^ 2 + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  obtain ⟨N₀, hN₀, hb⟩ := TernaryPatternBudget.uniform_bound C D k J hk ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base T hT hlabels hadm hprod
  have h := hb N hN L R hband hR α F U H base T hT hlabels
    (fun z hz ↦ (hadm z hz).toAdmissible) hprod
  have heq : (N : ℝ) ^ 3 * T ^ (-2 : ℝ) = (N : ℝ) ^ 3 / T ^ 2 := by
    rw [div_eq_mul_inv]
    congr 1
    norm_num
  simpa only [heq] using h

theorem source_centres_bound (C : ℝ) (D k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (base : Fin 3 → ℕ) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (T : ℝ), 1 ≤ T →
      ((sourceCentres N L R D k base U H T).card : ℝ) ≤
        (N : ℝ) ^ ε * ((N : ℝ) ^ 3 / T ^ 2 + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  obtain ⟨N₀, hN₀, hb⟩ := TernaryGroupBudget.uniform_bound C D k hk ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR base U H T hT
  have h := hb N hN L R hband hR (sourceCentres N L R D k base U H T) U H base T hT
    (fun X hX ↦ ((mem_sourceCentres N L R D k base U H T X).mp hX).1.toAdmissible)
    (fun X hX ↦ ((mem_sourceCentres N L R D k base U H T X).mp hX).2)
  have heq : (N : ℝ) ^ 3 * T ^ (-2 : ℝ) = (N : ℝ) ^ 3 / T ^ 2 := by
    rw [div_eq_mul_inv]
    congr 1
    norm_num
  simpa only [heq] using h

end PaperP1.TernaryGroupTheorem
