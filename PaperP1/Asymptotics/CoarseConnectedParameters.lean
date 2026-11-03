module

public import PaperP1.Asymptotics.CoarseConnectedTripleJointMassUnderInputs
public import PaperP1.Asymptotics.DirectCrossingSeedFamiliesUnderInputs
public import PaperP1.Asymptotics.FixedPrimitiveMassUnderInputs
public import PaperP1.Asymptotics.LowTwoPairSeedsUnderInputs
public import PaperP1.Asymptotics.DensePairCrossingFamiliesUnderInputs

/-! # A finite bundle of the existing geometric properties for the actual connected seed catalog -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoarseConnectedParameters

structure Parameters (R : ℕ) where
  primitive : Fin (R + 1) → DensePrimitiveTripleMassUnderInputs.Parameters
  tripleDense : DensePrimitiveTripleMassUnderInputs.Parameters
  tripleIsolatedPair : FinitePairDeficitInputs.Parameters
  tripleBadPair : FinitePairDeficitInputs.Parameters
  lowPair : FinitePairDeficitInputs.Parameters
  dense : DensePrimitiveTripleMassUnderInputs.Parameters
  densePair : FinitePairDeficitInputs.Parameters
  direct : Fin (R + 1) → DensePrimitiveTripleMassUnderInputs.Parameters
  directPair : Fin (R + 1) → FinitePairDeficitInputs.Parameters

structure Hypotheses {R : ℕ} (p : Parameters R) (ε : ℝ) : Prop where
  primitive : ∀ i, DensePrimitiveTripleMassUnderInputs.Hypotheses (p.primitive i)
  tripleDense : DensePrimitiveTripleMassUnderInputs.Hypotheses p.tripleDense
  tripleIsolatedPair : FinitePairDeficitInputs.Hypotheses p.tripleIsolatedPair
    (GeneralGraphHostCount.sizeCap (ε / 16384))
  tripleBadPair : FinitePairDeficitInputs.Hypotheses p.tripleBadPair
    (GeneralGraphHostCount.sizeCap (ε / 2048))
  lowPair : FinitePairDeficitInputs.Hypotheses p.lowPair (GeneralGraphHostCount.sizeCap (ε / 8192))
  dense : DensePrimitiveTripleMassUnderInputs.Hypotheses p.dense
  densePair : FinitePairDeficitInputs.Hypotheses p.densePair (GeneralGraphHostCount.sizeCap (ε / 4096))
  direct : ∀ i, DensePrimitiveTripleMassUnderInputs.Hypotheses (p.direct i)
  directPair : ∀ i, FinitePairDeficitInputs.Hypotheses (p.directPair i) (GeneralGraphHostCount.sizeCap (ε / 4096))

end PaperP1.CoarseConnectedParameters
