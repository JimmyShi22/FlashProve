-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/SwapHome.lean: the substitution at homeR b Z is the general substitution of
Johnson/LinkSim/Swap.lean at that input and the explicit link prover, by definition.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  premW_withLaid_of_layLink   the general statement (Spec.premW_layLink, Johnson/LinkSim/Swap.lean)
      implies the statement at homeR b Z (Spec.premW_withLaid,
      Johnson/LinkSim/AtHome/CompileFit.lean), by one call. The premise on the link's four clauses
      is given by linkFields_withLaid (Johnson/LinkSim/AtHome/CompileLaid.lean). It takes the
      general statement as a hypothesis, so it depends on neither proof; each of the two statements
      has its own proof in its own file.
  withLaidLink_eq   withLaidLink b Z a₀ c v₀ E is layLink at homeR b Z's compilation data and salt
      lengths, with the honest prover explicitLinkProver b Z and its coins enumerated by the enumeration
      picked by choice: by definition.
  fitSims_eq, fitNums_eq   fitSims Sm is laySims Sm (homeSim Z), and fitNums is layNums: by
      definition.

How it fits. A check that Johnson/LinkSim/Swap.lean's general statement loses nothing against
CompileFit.lean's statement at homeR b Z.

Limits. Those of Johnson/LinkSim/Swap.lean, Johnson/LinkSim/AtHome/CompileLaid.lean and
Johnson/LinkSim/AtHome/CompileFit.lean. Like them, it is an implication: see CompileFit.lean's
Limits.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileFit
import Johnson.LinkSim.Swap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace OnBytes.LinkSim.AtHome
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.WholeKey
open Johnson.Prover.Link (Kc)
open OnBytes.LinkSim (LinkFields layLink laySims layNums)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **The substitution at homeR b Z is the general one**: by definition. -/
theorem withLaidLink_eq
    (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
    (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL)) :
    withLaidLink b Z a₀ c v₀ E =
      layLink (homeR b Z).queryLayout (homeR b Z).compilerParameters a₀ c (explicitLinkProver b Z) (Member.pick Kc) v₀ E := rfl

/-- fitSims is laySims at the explicit simulator homeSim Z, by definition. -/
theorem fitSims_eq (Sm : Sims (homeR b Z).protocol) : fitSims Sm = laySims Sm (homeSim Z) := rfl

/-- fitNums is layNums, by definition. -/
theorem fitNums_eq (N : NumsW) : fitNums N = layNums N := rfl

/-- **The general statement gives the statement at homeR b Z**, by one call; its premise on the
link's four clauses is given by linkFields_withLaid. -/
theorem premW_withLaid_of_layLink (h : OnBytes.LinkSim.Spec.premW_layLink) : Spec.premW_withLaid :=
  fun b Z Sd cA a₀ Sm ok Gs Ryes c N v₀ E hP hv hE =>
    h (homeR b Z).Index (homeR b Z).Instance 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits
      (homeR b Z).linkRoundSplits (homeR b Z).queryLayout Sd cA (homeR b Z).compilerParameters a₀ Sm ok Gs Ryes c N (explicitLinkProver b Z)
      (Member.pick Kc) (homeSim Z) v₀ E hP (linkFields_withLaid b Z a₀ c v₀ E ok Gs)
      (Member.pick_ok _) hv hE

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.withLaidLink_eq
#print axioms OnBytes.LinkSim.AtHome.premW_withLaid_of_layLink
