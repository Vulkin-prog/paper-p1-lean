module

public import PaperP1.Arithmetic.OrdinaryCoverAtSystemFromExactSource
public import PaperP1.Arithmetic.SourceOrdinaryCoverPower
public import PaperP1.Arithmetic.UniformOrdinarySurfaceCover
public import PaperP1.Arithmetic.UniformExactSourceCoverFromP3
public import PaperP1.Arithmetic.OrdinaryRootSystemData

/-! # The full ordinary surface covering property follows from the exact source cover, with all constants chosen before coefficients and auxiliary degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformOrdinarySurfaceCoverFromExactSource

open HomogeneousSplitRadicalData

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

theorem of_exact (kmax K E : ℕ) (hE : 0 < E) (hK : K ≤ 2 * E)
    (h : ExactDegreeSourceSurfaceCover.UniformCover kmax E) : UniformOrdinarySurfaceCover.UniformCover kmax K := by
  intro δ hδ
  obtain ⟨B, A, hA, hsource⟩ := h (δ / (E : ℝ)) (div_pos hδ (Nat.cast_pos.mpr hE))
  refine ⟨B, A, hA, ?_⟩
  intro k hk d I j hd hI hj hne hsize
  dsimp only
  intro D hD H hH U hU
  let s := OrdinaryRootSystemData.radicands k E d I j
  have hlen : s.length = k := OrdinaryRootSystemData.length k E d I j
  let c : Fin k → ℚ := fun i ↦ (d i : ℚ)
  let J₀ : Fin k → Finset ℤ := fun i ↦ {j i}
  have hs : ∀ i : Fin s.length, s.get i = radicand (c (Fin.cast hlen i))
      (2 * E - ((I (Fin.cast hlen i)).card + (J₀ (Fin.cast hlen i)).card))
      (I (Fin.cast hlen i)) (J₀ (Fin.cast hlen i)) := OrdinaryRootSystemData.get k E d I j
  have hmin (i : Fin k) : 2 ≤ (I i).card + (J₀ i).card := by
    have hi := (hne i).card_pos
    simp only [J₀, Finset.card_singleton]
    omega
  have hdeg (i : Fin k) : (I i).card + (J₀ i).card ≤ 2 * E := by
    simpa only [J₀, Finset.card_singleton] using (hsize i).trans hK
  have hc (i : Fin k) : c i ≠ 0 := Int.cast_ne_zero.mpr (hd i)
  have hJ : Pairwise fun i t ↦ Disjoint (J₀ i) (J₀ t) := by
    intro i t hne
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact hne (hj ((Finset.mem_singleton.mp hz).symm.trans (Finset.mem_singleton.mp hz')))
  obtain ⟨V, curves, _hV, hdegree, hVbound, hcount, hpoint⟩ :=
    OrdinaryCoverAtSystemFromExactSource.exists_cover k E hE B A (δ / (E : ℝ)) (hsource hE k hk)
      s hlen c I J₀ hs hmin hdeg hc (fun i ↦ Or.inl (hne i)) hI hJ D hD H hH U hU
  refine ⟨V, curves, hdegree, ?_, ?_, hpoint⟩
  · simpa only [SourceOrdinaryCoverPower.height_power k E H hE 2 δ] using hVbound
  · simpa only [SourceOrdinaryCoverPower.height_power k E H hE 1 δ] using hcount

theorem of_hypersurface_covers (kmax K : ℕ)
    (hP3 : ∀ k : ℕ, k ≤ kmax → UniformP3HypersurfaceCover.UniformCover (2 ^ k * (K + 1) ^ 2)) :
    UniformOrdinarySurfaceCover.UniformCover kmax K :=
  of_exact kmax K (K + 1) (by omega) (by omega)
    (UniformExactSourceCoverFromP3.of_hypersurface_covers kmax (K + 1) hP3)

end PaperP1.UniformOrdinarySurfaceCoverFromExactSource
