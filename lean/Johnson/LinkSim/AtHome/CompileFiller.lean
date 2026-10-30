-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileFiller.lean: at homeR b Z some structure of parameters has the
explicit link prover and meets all eighteen clauses on the link; its other two provers are
placeholders.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has (namespace OnBytes.LinkSim.AtHome).
  link_all_met   for all b and all public files Z, with no premise: there are parameters a and c
      such that a's link prover is explicitLinkProver b Z; LinkCompile holds (the eleven clauses on the link's
      compilation data, round annotations and randomness); LinkFields holds with homeSim Z and both
      error terms 0, for every set ok of indices and every set Gs of seeds; and LinkBeside holds at
      62 and 62. In the proof the a is fillerAt b Z after the substitution of the link's
      components (withLaidLink).
  fillerAt b Z   explicit concrete parameters with placeholders: the three honest provers are
      placeholder provers that abort at every verifier message (idleHs,
      Johnson/Goal/Conditions/HomeIdle.lean); run values of a type with one element; empty public
      prefixes; every bound on proof-of-work attempts 0; one copy; the window 42, 1, 2 ^ 24; and
      enumerations with one value each for the tables' randomness, the salts and the runs' coins.
      Nothing is proved of its first table's sub-protocol or of its sessions.
  fillerNums b Z   the numbers of the clause coins: no public prefix, no random bit, and
      the padding body. (At these numbers PremW is false: see Limits.)

How it fits. The statements on the link at homeR b Z begin "for every structure of parameters a such
that ...". A statement of that form is vacuous if no such structure exists. withLaidLink
(Johnson/LinkSim/AtHome/CompileLaid.lean) makes one from any a₀; here is an a₀. Under
Johnson/LinkSim/ link_all_met is called by no file: it guards against that vacuity and is not a step
of any proof. The clause on the simulator is an instance of a proved theorem (linkFieldsHome,
Johnson/LinkSim/AtHome/Home.lean).

Limits.
  This guards against one kind of vacuity, and no more. It shows that some structure of
      parameters with the explicit link prover meets the eighteen clauses. It says nothing on
      whether the eighteen can be met together with the rest of the premises of index privacy. At
      these numbers the premises taken whole are false, whatever the other parameters. They ask
      that a table's salt's public prefix and random bits make up p.sMT bits, which is 256 or more
      at homeR b Z, and here both are empty (not_premW_fillerNums,
      Johnson/LinkSim/AtHome/CompileFillerNot.lean). So this pair is not part of any parameters
      that satisfy PremW.
  By inspection, not proved, more parts of the clause coins fail at these very parameters: the
      lengths of the leaf salts in the first table's sub-protocol and in the sessions (lenT, lenB:
      empty prefixes, no random bit); the distributions of these sub-protocols' randomness (coT,
      coB: one value against 256 or more uniform bits); and the enumeration of the tables'
      randomness, if that has two values (it lists one). The placeholder provers abort at every
      verifier message, so the probability of their aborts is 1, not a small number. Some of their
      other clauses hold vacuously. So there is no error (zetaW) to speak of at these parameters.
  The parameters for the first table's sub-protocol and for the sessions are placeholders. On
      whether the eighteen are all that PremW says of the link alone, see CompileHome.lean's limits;
      on the clauses that bind the link to the other two sub-protocols, see CompileSpec.lean's.

Notes.
  The general form is linkCompile_withLaid (Johnson/LinkSim/AtHome/CompileHome.lean); link_all_met
      is its instance at placeholder parameters. A c on the way to parameters that satisfy PremW
      must meet more than c.ℓ ≤ p.sMT: its public prefix and random bits must make up p.sMT bits
      (premW_salt_eq, CompileFillerNot.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileHome
import Johnson.Goal.Conditions.HomeIdle

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
open OnBytes.LinkSim (LinkFields LinkBeside)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/- These definitions are made irreducible here, so that Lean does not unfold them while it
elaborates. This is for speed; the kernel still checks every proof. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **Explicit concrete parameters with placeholders**: the three honest provers abort at every
verifier message, every bound on attempts is 0, and there is one copy. -/
def fillerAt : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits where
  Hs := idleHs b Z
  dc := ⟨fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _⟩
  b₀ := fillB b Z
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 0
  M := 0
  nm := id
  RV := Unit
  okV := fun _ => True
  rvT := fun _ => ()
  rvL := fun _ => ()
  rvB := fun _ => ()
  startT := fun _ _ _ _ => []
  startL := fun _ _ _ _ => []
  startB := fun _ _ _ _ => []
  pvT := fun _ => ()
  pvL := fun _ => ()
  pvB := fun _ => ()
  rtail := fun _ => []
  nR := 42
  nK := 1
  nJ := 2 ^ 24
  fill := []
  ri := ⟨0, fun _ => padB b Z ((riDigits Z).e 0)⟩
  sl := ⟨0, fun _ _ => []⟩
  kT := Member.pick _
  kL := Member.pick _
  kB := Member.pick _
  coT := ⟨0, fun _ => ⟨[], fun _ _ _ _ => [], fillB b Z, 0, [], []⟩⟩
  coL := ⟨0, fun _ => ⟨[], fun _ _ _ _ => [], fillB b Z, 0, [], []⟩⟩
  coB := ⟨0, fun _ => ⟨[], fun _ _ _ _ => [], fillB b Z, 0, [], []⟩⟩

/-- The numbers of the clause coins: no public prefix, no random bit, and the padding
body. -/
def fillerNums : CoinNums (homeR b Z).LeafBody :=
  ⟨[], 0, 0, fillB b Z, fillB b Z, fillB b Z, 0, 0, 0⟩

/-- **The eighteen clauses on the link are met at one structure of parameters**, with the
explicit link prover: no premise. -/
theorem link_all_met :
    ∃ (a : AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits)
      (c : CoinNums (homeR b Z).LeafBody),
      a.Hs.Lk = explicitLinkProver b Z ∧ LinkCompile (homeR b Z).queryLayout (homeR b Z).compilerParameters a c ∧
      (∀ (ok : (homeR b Z).Index → Prop) (Gs : (homeR b Z).protocol.OutOfDomainSeed → Prop),
        LinkFields a (homeSim Z) (homeR b Z).queryLayout ok Gs 0 0) ∧
      LinkBeside (homeR b Z).protocol 62 62 := by
  obtain ⟨E, hE⟩ := runBits_listed 256 (fillerAt b Z).nR (fillerAt b Z).nK (fillerAt b Z).nJ
    (homeR b Z).compilerParameters.sFS (fillerNums b Z).ℓ (fillerNums b Z).ℓr (homeR b Z).queryLayout.depthReqL
  exact ⟨withLaidLink b Z (fillerAt b Z) (fillerNums b Z) () E, fillerNums b Z, rfl,
    linkCompile_withLaid b Z (fillerAt b Z) (fillerNums b Z) () E hE trivial (Nat.zero_le _)
      le_rfl le_rfl le_rfl,
    fun ok Gs => linkFields_withLaid b Z (fillerAt b Z) (fillerNums b Z) () E ok Gs,
    home_beside b Z⟩

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.link_all_met
