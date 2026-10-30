-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/LaidAll.lean: the premises of index privacy are satisfied at every value of the
public reading by one honest side whose link prover is the explicit one and whose other two provers
are placeholder provers, which send fixed messages, with one bound on the error for all values.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has.
premAll_laid: for every b and all public files Z in scope, if M + 1 ≤ 710324, s1 ≤ 688127, ℓ is at
most the length of a leaf's salt and E lists each value once, the premises of index privacy at every
value d of the public reading (PremAll, Johnson/FrontRoad/PremAt.lean) hold of the family homeT b Z
and the parameters laidSides (Johnson/FrontRoad/LaidSides.lean). The range is all indices, no
out-of-domain seed is set aside, and the set Ryes of true pairs is any set.
zetaLe_laid: at the same parameters, for Z in scope and 256 ≤ ℓ, the error zetaW is, at every d, at
most boundZ (9 + CT + CL + CB) M t n (E2E/ZetaAtCaps.lean) for up to s1 requests, where CT, CL and
CB bound the search limits from above.
zetaLe_laid_own: at every d the error is at most (it is equal: zeta_told) the error zetaW at homeR b
Z's own data for out-of-domain seeds, for every number of requests.

How it fits. The three are E2E/LinkLaidTold.lean's premW_laid_told, zeta_laid_told and zeta_told,
said for all d at once in the words of this folder. They give parameters that satisfy the main
premise of this folder's theorems on index privacy. Johnson/FrontRoad/LaidId.lean applies
threeOfId_of_laws (Johnson/FrontRoad/IdAlone.lean) to them. Not among the release's goal statements.

Limits.
  Two of the three provers are placeholder provers, which send fixed messages. No verifier is shown
      to accept their proofs, and no completeness is proved at these parameters.
  This folder's premises of completeness (HonAll, Johnson/FrontRoad/HonAt.lean) are not satisfied at
      these parameters, at any Dok that has a member, for ℓ from 1 to the length of a leaf's salt:
      its clause side fails
      (not_sideFit_laid, E2E/LinkLaidAny.lean).
      The reason, by inspection: that clause (SideFit, Johnson/WholeKey/Complete.lean) asks that a
      leaf's salt has the full length at every round and leaf, outside the window of sampled bits
      too. There the salt is a start of sMT - ℓ zeros and the filler, which is empty at laidAt. The
      clause also asks the starts' length at rounds beyond nR, where PremW stops at nR. Index
      privacy is not touched.
  These parameters are the same at every d. An honest side whose salts hold the digest that is read
      depends on d, and nothing here is proved of such a side.
  All limits of E2E/LinkLaidTold.lean and of premW_withLaid
      (Johnson/LinkSim/AtHome/CompileFit.lean).
-/
import E2E.LinkLaidTold
import Johnson.FrontRoad.LaidSides

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.LinkLaid
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput LayoutsByPublicReading)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (flashProveData homeR homeT flashProveDescription allZeroDigest)
open AtPublicFiles.LinkLaid.Told (premW_laid_told zeta_told zeta_laid_told)

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles) (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- With two placeholder provers, which send fixed messages, for Z in scope, M + 1 ≤ 710324,
s1 ≤ 688127, ℓ at most the length of a leaf's salt and an E that lists each value once: **the
premises of index privacy hold at every d.** -/
theorem premAll_laid (i₀ : (homeR b Z).Index) (scope : InScope Z = true) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremAll (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀) (fun _ => True) Ryes fun _ => True :=
  fun d _ => premW_laid_told b Z d b₀ M s1 ℓ ℓr capT capL capB E scope hM hs hℓ hE Ryes

/-- For Z in scope, 256 ≤ ℓ and search limits of at most CT, CL and CB: **one bound on the error for
all d.** -/
theorem zetaLe_laid (i₀ : (homeR b Z).Index) (scope : InScope Z = true) (CT CL CB : ℕ) (hℓ : 256 ≤ ℓ)
    (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL) (hB : ∀ i, capB i ≤ CB) :
    ZetaLe (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀) (fun _ => True)
      (upTo s1 (boundZ (9 + CT + CL + CB) M)) := by
  intro d _ t n
  by_cases hn : n ≤ s1
  · rw [upTo_of_le hn]
    exact zeta_laid_told b Z d b₀ M s1 ℓ ℓr capT capL capB E scope CT CL CB hℓ hT hL hB t n hn
  · unfold upTo
    rw [if_neg hn]
    exact le_top

/-- **The error is one function at all d**: the error at homeR b Z's own data. -/
theorem zetaLe_laid_own (i₀ : (homeR b Z).Index) :
    ZetaLe (laidSides b Z b₀ M s1 ℓ ℓr capT capL capB E i₀) (fun _ => True)
      (zetaW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).compilerParameters (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
        (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0))) :=
  fun d _ t n => le_of_eq (congrFun (congrFun (zeta_told b Z d _ _ _) t) n)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.premAll_laid
#print axioms OnBytes.FrontRoad.zetaLe_laid
#print axioms OnBytes.FrontRoad.zetaLe_laid_own
