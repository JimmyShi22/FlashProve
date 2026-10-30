-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileLaid.lean: the substitution of the link's components at homeR b Z, and
the clauses that it meets.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  withLaidLink b Z a₀ c v₀ E   a₀ with the link's seven components replaced (the table:
      Johnson/LinkSim/Swap.lean), with H := explicitLinkProver b Z (Johnson/LinkSim/AtHome/SpecHome.lean) and
      the coins' enumeration picked by choice. The first table's and the sessions' components, the
      bounds on proof-of-work attempts, the window and all numbers are a₀'s.
  linkFields_withLaid   for all ok and Gs, the link's four clauses on its honest prover and
      simulator (LinkFields) hold of that same structure with homeSim Z, with both error terms 0.
      So these four and the eleven of LinkCompile speak of one structure of parameters.
  withLaidLink_laid   the substitution meets LaidLink (Johnson/LinkSim/AtHome/CompileSpec.lean), if
      E lists each value once, v₀ is well formed, c.ℓ ≤ p.sMT, 42 ≤ a₀.nR, 1 ≤ a₀.nK and
      2 ^ 24 ≤ a₀.nJ. These are what LaidLink asks of the components that the link shares with the
      other two sub-protocols.
  coinRows_of_laid   for every protocol structure, LaidLink gives the four clauses of LinkCompile
      on the link's coins (LinkCoinRows: kL, okL, lenL, coL). The picked enumeration lists each
      coin once (pick_ok, Johnson/WholeKey/Member.lean); the constant run value is well formed; a
      public prefix of p.sMT - c.ℓ bits and c.ℓ random bits make p.sMT bits; and coinsPre has the
      required distribution (runLaw_coinsPre, Johnson/WholeKey/CoinLaws.lean).
  runBits_listed   for all sizes, the random bits of a hashed run can be enumerated with each value
      once, so a suitable E always exists.
  withLaidLink_side   the new link prover is explicitLinkProver b Z, by definition.

How it fits. withLaidLink and linkFields_withLaid serve premW_withLaid, and runBits_listed serves
premW_withLaid_some: Johnson/LinkSim/AtHome/CompileFit.lean uses them. coinRows_of_laid and
withLaidLink_laid serve linkCompileHome and linkCompile_withLaid
(Johnson/LinkSim/AtHome/CompileHome.lean), and through them, under Johnson/LinkSim/, link_all_met
(Johnson/LinkSim/AtHome/CompileFiller.lean) alone. Johnson/LinkSim/AtHome/SwapHome.lean also uses
linkFields_withLaid. linkFields_withLaid is an instance of linkFieldsHome
(Johnson/LinkSim/AtHome/Home.lean).

Limits.
  A structure a₀ to start from is a premise. That parameters for the first table's sub-protocol and
      for the sessions exist at homeR b Z, with anything proved of them, is not said.
  Whether the substituted values are the programs' is not said (see CompileSpec.lean's limits).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileSpec
import Johnson.LinkSim.AtHome.Home

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
open OnBytes.LinkSim (LinkFields)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

section General
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The four clauses of LinkCompile on the link's coins. -/
structure LinkCoinRows (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) : Prop where
  kL : a.kL.OK
  okL : ∀ κ, a.okV (a.rvL κ)
  lenL : ∀ v i b s, a.okV v → i < a.nR → s.length = p.sFS →
    (a.startL v i b s).length + c.ℓ = p.sMT
  coL : RunLaw a.coL a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL

/-- **They follow from LaidLink**, for every protocol structure. -/
theorem coinRows_of_laid {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {p : Params}
    {a : AtRecs lam L Bd aT aL} {c : CoinNums Bd} {v₀ : a.RV} (h : LaidLink W p a c v₀) :
    LinkCoinRows W p a c where
  kL := by
    rw [h.kL]
    exact Member.pick_ok _
  okL := fun κ => by
    rw [h.rvL κ]
    exact h.okV
  lenL := fun v i b s _ _ _ => by
    rw [h.startL v i b s]
    exact Nat.sub_add_cancel h.free
  coL := by
    obtain ⟨E, hE, e⟩ := h.coL
    rw [e]
    exact runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ E hE

/-- The random bits of a hashed run's coins can be listed, each value once. -/
theorem runBits_listed (lam nR nK nJ sFS ℓ ℓr dq : ℕ) :
    ∃ E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq), E.OK := by
  haveI : Nonempty (RunBits lam nR nK nJ sFS ℓ ℓr dq) :=
    ⟨(fun _ => false, fun _ _ _ _ _ => false, fun _ => false, fun _ _ => false)⟩
  haveI : Fintype (RunBits lam nR nK nJ sFS ℓ ℓr dq) := Fintype.ofFinite _
  exact ⟨Member.pick _, Member.pick_ok _⟩

end General

/-- **a₀ with the link's seven components replaced**: the honest prover by explicitLinkProver b Z and its
Decidable instance for the abort set by Classical.dec; both readings of the run value by v₀; the
salt prefixes by zeros; the coins' enumeration by one picked by choice; the hashed run's randomness
by coinsPre at E. -/
def withLaidLink (b : PublicFiles → ℕ) (Z : PublicFiles)
    (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
    (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
    (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL)) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits where
  Hs := ⟨a₀.Hs.T, explicitLinkProver b Z, a₀.Hs.B⟩
  dc := ⟨a₀.dc.T, fun _ _ _ => Classical.dec _, a₀.dc.B⟩
  b₀ := a₀.b₀
  capT := a₀.capT
  capL := a₀.capL
  capB := a₀.capB
  M := a₀.M
  nm := a₀.nm
  RV := a₀.RV
  okV := a₀.okV
  rvT := a₀.rvT
  rvL := fun _ => v₀
  rvB := a₀.rvB
  startT := a₀.startT
  startL := fun _ _ _ _ => List.replicate ((homeR b Z).compilerParameters.sMT - c.ℓ) false
  startB := a₀.startB
  pvT := a₀.pvT
  pvL := fun _ => v₀
  pvB := a₀.pvB
  rtail := a₀.rtail
  nR := a₀.nR
  nK := a₀.nK
  nJ := a₀.nJ
  fill := a₀.fill
  ri := a₀.ri
  sl := a₀.sl
  kT := a₀.kT
  kL := Member.pick Kc
  kB := a₀.kB
  coT := a₀.coT
  coL := coinsPre a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL c.padL
    c.slotL a₀.fill E
  coB := a₀.coB

variable (b : PublicFiles → ℕ) (Z : PublicFiles)
  (a₀ : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
  (c : CoinNums (homeR b Z).LeafBody) (v₀ : a₀.RV)
  (E : Enum (RunBits 256 a₀.nR a₀.nK a₀.nJ (homeR b Z).compilerParameters.sFS c.ℓ c.ℓr (homeR b Z).queryLayout.depthReqL))

/-- Its link's honest prover is the explicit prover explicitLinkProver b Z. -/
theorem withLaidLink_side : (withLaidLink b Z a₀ c v₀ E).Hs.Lk = explicitLinkProver b Z := rfl

/-- **The substitution meets LaidLink**, if a₀ and c meet what LaidLink asks of the components that
the link shares with the other two sub-protocols. -/
theorem withLaidLink_laid (hE : E.OK) (hv : a₀.okV v₀) (hf : c.ℓ ≤ (homeR b Z).compilerParameters.sMT)
    (hR : 42 ≤ a₀.nR)
    (hK : 1 ≤ a₀.nK) (hJ : 2 ^ 24 ≤ a₀.nJ) :
    LaidLink (homeR b Z).queryLayout (homeR b Z).compilerParameters (withLaidLink b Z a₀ c v₀ E) c v₀ where
  kL := rfl
  rvL := fun _ => rfl
  startL := fun _ _ _ _ => List.length_replicate
  coL := ⟨E, hE, rfl⟩
  okV := hv
  free := hf
  nR := hR
  nK := hK
  nJ := hJ

/-- **The link's four clauses (LinkFields) hold of that same structure**, with homeSim Z and both
error terms 0. -/
theorem linkFields_withLaid (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop) :
    LinkFields (withLaidLink b Z a₀ c v₀ E) (homeSim Z) (homeR b Z).queryLayout ok Gs 0 0 :=
  linkFieldsHome b Z (withLaidLink b Z a₀ c v₀ E) v₀ rfl (fun _ => rfl) (fun _ => rfl) ok Gs

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.coinRows_of_laid
#print axioms OnBytes.LinkSim.AtHome.withLaidLink_laid
#print axioms OnBytes.LinkSim.AtHome.linkFields_withLaid
