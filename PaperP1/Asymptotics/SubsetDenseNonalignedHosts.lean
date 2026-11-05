module

public import PaperP1.Asymptotics.SubsetComponentIntersectionLower
public import PaperP1.Asymptotics.BoundedWidthPrimeConstraintCost
public import PaperP1.Asymptotics.BoundedWidthNonalignedPairs
public import PaperP1.Arithmetic.ShiftedWindowNonalignment
public import PaperP1.Arithmetic.ExpandedAsymmetricSupportEnvelope
public import PaperP1.Arithmetic.BoundedWidthWindows
public import PaperP1.Asymptotics.EnlargedOffsetRegime

/-! # Dense components on two actual bounded-width subsets force subpower many nonaligned centers

Unused bookkeeping positions are pinned throughout. The actual subsets first
supply their own even intersection, which is embedded in windows of radius R.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SubsetDenseNonalignedHosts

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model
  PaperP1.SubsetComponentHostData PaperP1.AsymmetricEnvelopeGraph PaperP1.LocalDefectBound

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (S : Submodule F₂ T) :
    AddCommGroup S := Submodule.addCommGroup S
local instance {T : Type*} [AddCommGroup T] [Module F₂ T] (S : Submodule F₂ T) : Module F₂ S := S.module

theorem uniform_dense (Q : ℕ) (_hQ : 1 ≤ Q) (C ε η : ℝ) (Dwidth Dcut : ℕ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ Dwidth * (L + 1) →
      1 ≤ R → H ≤ Dcut * (L + 1) →
      ∀ old new : ℕ → Finset ℕ,
      (∀ x ∈ ExpandedAsymmetricSupportEnvelope.block N Q, ∀ n ∈ old x, |(n : ℤ) - x| ≤ (R : ℤ)) →
      (∀ y ∈ dyadicBlock N, ∀ n ∈ new y, |(n : ℤ) - y| ≤ (R : ℤ)) →
      ∀ F : Finset (ℕ × ℕ),
      (∀ p ∈ F, p.1 ∈ ExpandedAsymmetricSupportEnvelope.block N Q ∧ p.2 ∈ dyadicBlock N) →
      (∀ p ∈ F, ¬CompressedTargetAlignment.Aligned Dwidth p.1 p.2 L) →
      (∀ p ∈ F, η * ((L + 1 : ℕ) : ℝ) ≤ (nontrivial p.1 p.2 H R (old p.1) (new p.2)).card) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε := by
  let A := 2 * (Q + 1)
  obtain ⟨NH, _hNH, hh⟩ := BoundedWidthNonalignedPairs.uniform_intersection_hosts A (2 * Dwidth + 1)
    (by dsimp [A]; omega) (by omega) C (η / 2) ε (by positivity) hε
  obtain ⟨NC, _hNC, hc⟩ := BoundedWidthPrimeConstraintCost.uniform_cost Dcut C (η / 2) (by positivity)
  obtain ⟨NW, hw⟩ := EnlargedOffsetRegime.uniform_widths C (2 * Dwidth)
  refine ⟨3 + NH + NC + NW, by omega, ?_⟩
  intro N hN L H R hband hR hRpos hH old new hold hnew F hF hnon hdense
  classical
  have hRlarge : 2 * R ≤ (2 * Dwidth) * (L + 1) := by nlinarith only [hR]
  have hsmall : 2 * R < N := (hw N (by omega) L (2 * R) hband hRlarge).2.2
  have hcap : 2 * R ≤ (L + 1) ^ 3 :=
    (hw N (by omega) L R hband (by nlinarith only [hR])).2.1
  have hcenters (p : ℕ × ℕ) (hp : p ∈ F) : R < p.1 ∧ R < p.2 := by
    have hx := (mem_Ico.mp (hF p hp).1).1
    have hy := (mem_Ico.mp (hF p hp).2).1
    omega
  let shift : ℕ × ℕ → ℕ × ℕ := fun p ↦ (start p.1 R, start p.2 R)
  let P := F.image shift
  have hbox (p : ℕ × ℕ) (hp : p ∈ F) :
      (N ≤ A * (shift p).1 ∧ (shift p).1 ≤ A * N) ∧
        (N ≤ A * (shift p).2 ∧ (shift p).2 ≤ A * N) := by
    have hx := mem_Ico.mp (hF p hp).1
    have hy := mem_Ico.mp (hF p hp).2
    have hlowx : N ≤ 2 * start p.1 R := by dsimp [start]; omega
    have hlowy : N ≤ 2 * start p.2 R := by dsimp [start]; omega
    have hax : N ≤ A * start p.1 R := hlowx.trans (Nat.mul_le_mul_right _ (by dsimp [A]; omega))
    have hay : N ≤ A * start p.2 R := hlowy.trans (Nat.mul_le_mul_right _ (by dsimp [A]; omega))
    have hux : start p.1 R ≤ (Q + 1) * N := by
      have he : (Q + 1) * N = N + Q * N := by ring
      rw [he]
      dsimp [start]
      omega
    have huy : start p.2 R ≤ 2 * N := by dsimp [start]; omega
    exact ⟨⟨hax, hux.trans (Nat.mul_le_mul_right N (by dsimp [A]; omega))⟩,
      ⟨hay, huy.trans (Nat.mul_le_mul_right N (by dsimp [A]; omega))⟩⟩
  have hinter (p : ℕ × ℕ) (hp : p ∈ F) :
      (η / 2) * L ≤ (Module.finrank F₂
        ↥(squareClassSpace (shift p).1 (2 * R) ⊓ squareClassSpace (shift p).2 (2 * R)) : ℝ) := by
    let U := old p.1
    let V := new p.2
    let : Module.Finite F₂ (FiniteEvenSquareClasses.space U) :=
      Module.Finite.range (EvenImage.evenMap (FiniteEvenSquareClasses.data U))
    have hcomp : ((nontrivial p.1 p.2 H R U V).card : ℝ) ≤
        Module.finrank F₂ ↥(FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V) +
          primeCount (10 * (H + 1)) + 2 := by
      exact_mod_cast SubsetComponentIntersectionLower.finite_bound p.1 p.2 H R U V
    have hU : FiniteEvenSquareClasses.space U ≤ squareClassSpace (shift p).1 (2 * R) := by
      apply BoundedWidthWindows.space_le_window U p.1 R (hcenters p hp).1.le
      intro n hn
      have he := hold p.1 (hF p hp).1 n hn
      rw [Int.abs_eq_natAbs] at he
      exact_mod_cast he
    have hV : FiniteEvenSquareClasses.space V ≤ squareClassSpace (shift p).2 (2 * R) := by
      apply BoundedWidthWindows.space_le_window V p.2 R (hcenters p hp).2.le
      intro n hn
      have he := hnew p.2 (hF p hp).2 n hn
      rw [Int.abs_eq_natAbs] at he
      exact_mod_cast he
    have hrank : (Module.finrank F₂ ↥(FiniteEvenSquareClasses.space U ⊓ FiniteEvenSquareClasses.space V) : ℝ) ≤
        Module.finrank F₂ ↥(squareClassSpace (shift p).1 (2 * R) ⊓ squareClassSpace (shift p).2 (2 * R)) := by
      exact_mod_cast Submodule.finrank_mono (inf_le_inf hU hV)
    have hcost := hc N (by omega) L H hband hH
    have hd := hdense p hp
    push_cast at hd
    nlinarith only [hcomp, hrank, hcost, hd, hη]
  have hbound := hh N (by omega) L hband (2 * R) (by omega)
    (by nlinarith only [hR, Nat.zero_le L]) P (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact hbox p hp) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact ShiftedWindowNonalignment.of_compressed (hcenters p hp).1 (hcenters p hp).2
        hR hcap (hnon p hp)) (by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
      exact hinter p hp)
  have hinj : Set.InjOn shift (F : Set (ℕ × ℕ)) := by
    intro p hp q hq he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    have hp' := hcenters p hp
    have hq' := hcenters q hq
    apply Prod.ext <;> dsimp [shift, start] at hx hy <;> omega
  simpa only [P, card_image_of_injOn hinj] using hbound

end PaperP1.SubsetDenseNonalignedHosts
