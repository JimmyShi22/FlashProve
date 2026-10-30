-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileHome.lean: at homeR b Z, the link meets all eleven clauses of
LinkCompile after the substitution; the proof of Spec.linkCompileHome.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  linkCompileHome   proves Spec.linkCompileHome (Johnson/LinkSim/AtHome/CompileSpec.lean): at
      homeR b Z, for all a, c and v₀, LaidLink implies LinkCompile.
  linkCompile_withLaid   at one structure of parameters: for every a₀, c, v₀ and every enumeration E
      of the random bits that lists each value once, if v₀ is well formed, c.ℓ ≤ compilerParameters.sMT, 42 ≤ a₀.nR,
      1 ≤ a₀.nK and 2 ^ 24 ≤ a₀.nJ, then withLaidLink b Z a₀ c v₀ E meets LinkCompile. With
      linkFields_withLaid (Johnson/LinkSim/AtHome/CompileLaid.lean: the four clauses on the honest
      prover and simulator, both error terms 0) and home_beside
      (Johnson/LinkSim/AtHome/HomeTies.lean: the three on the protocol), the link meets eighteen
      clauses at one structure of parameters.
  Other names: freeL_fullD, backL_fullD, winL_fullD, roundsL_fullD (at the input that
      innerCompilerInputAtFullSize builds, for all round data); home_freeL, home_backL, home_winL, home_roundsL,
      home_wireL (at homeR b Z).

How the eleven are proved. freeL, backL, winL and roundsL apply the facts of
Johnson/LinkSim/AtHome/CompileWire.lean on the link's compilation data (readsFree_wqW,
noncesBack_wqW, withinWin_wqW with fr_one and fr_leaves, and length_full); backL holds for every
bound on proof-of-work attempts. okgL, fmtL and cohL are calls of wiresFit_home
(Johnson/Prover/At/HomeAt.lean), which has no premise and is stated at one reading of the public
strings, on which these three do not depend. kL, okL, lenL and coL hold by the substitution
(coinRows_of_laid, CompileLaid.lean).

How it fits. linkCompileHome and linkCompile_withLaid serve link_all_met
(Johnson/LinkSim/AtHome/CompileFiller.lean) and, under Johnson/LinkSim/, nothing else.
Johnson/LinkSim/AtHome/CompileFit.lean imports this file, but its premW_withLaid copies the eleven
clauses from its own premise.

Limits.
  The clauses that bind the link to the first table's sub-protocol and to the sessions, the two
      query budgets among them, are not proved here (see Johnson/LinkSim/AtHome/CompileSpec.lean's
      limits).
  That these eighteen are all that PremW says of the link alone is by inspection of PremW's text,
      not proved. Besides them, five parts of the base's well-formedness conditions
      (wires.base) name the link's compilation data alone: LinkInBase,
      Johnson/LinkSim/AtHome/CompileBase.lean, where home_linkInBase proves them with no premise.
  Whether the substituted values are the programs' is not said (see CompileSpec.lean's limits).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileLaid
import Johnson.LinkSim.AtHome.CompileWire
import Johnson.Prover.At.HomeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.LinkSim.AtHome
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## At the input that innerCompilerInputAtFullSize builds, for all data of the three proof files -/

section FullD
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ}
  {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
  (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P)

/-- The positions of its own oracle messages that the link's verifier reads do not depend on
nonces. -/
theorem freeL_fullD :
    ReadsFree (batLC (innerCompilerInputAtFullSize T).protocol (innerCompilerInputAtFullSize T).linkRoundSplits) (wLC (innerCompilerInputAtFullSize T).queryLayout).sh :=
  readsFree_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec

/-- Each number is read back from the plain part into which it was written, for every bound on
attempts. -/
theorem backL_fullD (cap : ℕ → ℕ) (i : ℕ) :
    NoncesBack (innerCompilerInputAtFullSize T).protocol.link.shape (innerCompilerInputAtFullSize T).linkRoundSplits
      (wLC (innerCompilerInputAtFullSize T).queryLayout).sh cap i :=
  noncesBack_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec cap i

/-- All trees lie within the window, if each round's trees and each tree's leaves do. -/
theorem winL_fullD (nK nJ : ℕ) (h1 : ∀ d ∈ ds, d.trees.length ≤ nK)
    (h2 : ∀ d ∈ ds, ∀ s ∈ d.trees, 2 ^ s.a ≤ nJ) :
    WithinWin nK nJ (innerCompilerInputAtFullSize T).protocol.link.shape (innerCompilerInputAtFullSize T).linkRoundSplits
      (wLC (innerCompilerInputAtFullSize T).queryLayout).sh :=
  withinWin_wqW (ckP .two) K (chalP .two K) ds frS.P.T.a xs dec nK nJ h1 h2

/-- The link has one round more than the list of rounds has members. -/
theorem roundsL_fullD : (innerCompilerInputAtFullSize T).protocol.link.shape.length = ds.length + 1 :=
  length_linkW (ckP .two) ds frS.P.T.a xs dec

end FullD

end OnBytes.LinkSim.AtHome

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.WholeKey
open Johnson.Prover.Link (fr_one)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-! ## At homeR b Z -/

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

set_option maxRecDepth 100000 in
/-- The positions of its own oracle messages that the link's verifier reads do not depend on
nonces. -/
theorem home_freeL :
    ReadsFree (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout).sh :=
  freeL_fullD ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])

set_option maxRecDepth 100000 in
/-- Each number is read back from the plain part into which it was written, for every bound on
attempts. -/
theorem home_backL (cap : ℕ → ℕ) :
    NoncesBack (homeR b Z).protocol.link.shape (homeR b Z).linkRoundSplits (wLC (homeR b Z).queryLayout).sh cap 0 :=
  backL_fullD ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []) cap 0

set_option maxRecDepth 100000 in
/-- All trees of the link's rounds lie within a window of one tree per round component and 2 ^ 24
leaves per tree, or a wider one. -/
theorem home_winL (nK nJ : ℕ) (hK : 1 ≤ nK) (hJ : 2 ^ 24 ≤ nJ) :
    WithinWin nK nJ (homeR b Z).protocol.link.shape (homeR b Z).linkRoundSplits (wLC (homeR b Z).queryLayout).sh :=
  winL_fullD ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []) nK nJ (fun d hd => (fr_one d hd).trans hK)
    fun d hd s hs => (fr_leaves d hd s hs).trans hJ

set_option maxRecDepth 100000 in
/-- The link has 42 rounds. -/
theorem home_roundsL : (homeR b Z).protocol.link.shape.length = 42 :=
  length_full (_root_.Run.ckP .two) frS.P.T.a PV.EntryFive.xsF (dataAtFiles flashProveData Z).dec

/-- The link's compilation data is well formed, and its round annotations have formats and fit
together: by a call of wiresFit_home. -/
theorem home_wireL :
    (wLC (homeR b Z).queryLayout).OKG ∧ (homeR b Z).linkRoundSplits.Fmt ∧ (homeR b Z).linkRoundSplits.Coherent :=
  have h := wiresFit_home b Z ((homeT b Z).Pub.det fun _ _ _ => false)
  ⟨h.oka.Lk, h.fmt.2.1, h.coh.2.1⟩

/-- Proves Spec.linkCompileHome: at homeR b Z, LaidLink implies LinkCompile. -/
theorem linkCompileHome : Spec.linkCompileHome := fun b Z a _ _ h =>
  { freeL := home_freeL b Z
    okgL := (home_wireL b Z).1
    fmtL := (home_wireL b Z).2.1
    cohL := (home_wireL b Z).2.2
    backL := home_backL b Z a.capL
    kL := (coinRows_of_laid h).kL
    okL := (coinRows_of_laid h).okL
    lenL := (coinRows_of_laid h).lenL
    coL := (coinRows_of_laid h).coL
    roundsL := (le_of_eq (home_roundsL b Z)).trans h.nR
    winL := home_winL b Z a.nK a.nJ h.nK h.nJ }

/-- **At one structure of parameters**: a₀ with the link's components replaced (withLaidLink) meets
the eleven clauses, if a₀ and c meet what LaidLink asks of the shared components. -/
theorem linkCompile_withLaid
    (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
    (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL))
    (hE : E.OK) (hv : a₀.okV v₀) (hf : c.ℓ ≤ (homeR b Z).compilerParameters.sMT) (hR : 42 ≤ a₀.nR)
    (hK : 1 ≤ a₀.nK) (hJ : 2 ^ 24 ≤ a₀.nJ) :
    LinkCompile (homeR b Z).queryLayout (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) c :=
  linkCompileHome b Z _ c v₀ (withLaidLink_laid b Z a₀ c v₀ E hE hv hf hR hK hJ)

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.home_freeL
#print axioms OnBytes.LinkSim.AtHome.home_backL
#print axioms OnBytes.LinkSim.AtHome.home_winL
#print axioms OnBytes.LinkSim.AtHome.home_roundsL
#print axioms OnBytes.LinkSim.AtHome.home_wireL
#print axioms OnBytes.LinkSim.AtHome.linkCompileHome
#print axioms OnBytes.LinkSim.AtHome.linkCompile_withLaid
