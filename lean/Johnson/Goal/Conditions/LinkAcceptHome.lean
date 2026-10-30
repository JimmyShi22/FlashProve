-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LinkAcceptHome.lean: at the honest link prover's own input in homeR b Z, the
link protocol's interactive verifier, at link_yes' decision, accepts the explicit honest prover's
run at all challenges that pass the proof-of-work checks (link_accLaw_home), and there is such a run
(link_accepts_home). At the library's full-size parameter set. The protocol:
Johnson/Prover/Link/LinkFrame.lean. link_yes: Johnson/Prover/Link/LinkJoinF.lean.
What the link is, where these files stand, and the common limits 1 to 4:
Johnson/Prover/Link/LinkYesStm.lean.

What this file has. link_accLaw_home. Take any b, any public files Z, any index i of homeR b Z, any
two values q, q' of the encoding randomness (the encoder's second argument, HolographicProtocol's type EncodingRandomness; free
variables here), any two seeds e, e' and any value C of the prover's free parameters (LCoins,
Johnson/Prover/Link/LinkAll.lean); and any K and chal, the two parameters of the compilation data
wqW. Let the instance be the two OOD samples (recOf i q e, recOf i q' e'), the input oracles the two
encodings (encodeIndex i q, encodeIndex i q'), and the prover's input these with the honest row polynomials. Then
AccLaw (Johnson/Prover/Law/Defs.lean) holds of the strategy stratOf at linkNext, with the set B
empty. In words: the interactive verifier accepts every transcript that is the strategy's own run
but for nonces, with all proof-of-work checks passed. There is no premise but AccLaw's own, and no
premise on Z: neither InScope nor protocolDataWellFormed is asked. That verifier does not depend on Z. That the
link decision inside dataAtFiles flashProveData Z is this decision is proved under these two tests (dec_at_D,
Johnson/Goal/Conditions/LinkDecAt.lean); the accept for the link of homeR b Z is linkFits_at's field
accL. No further challenge is excepted and there is no error term.
link_accepts_home. For the same b, Z, i, q, q', e, e' and C there are challenges ρ at which that
verifier accepts the strategy's own run. It has no premise. So link_accLaw_home is not vacuous at
any of these inputs.

How it fits. link_accLaw_home is link_accLaw (Johnson/Prover/Link/LinkAccept.lean) with its two
premises proved by accept_met_home (Johnson/Goal/Conditions/LinkAcceptMet.lean). link_accepts_home
applies it to the run that accLaw_link_run gives (Johnson/Prover/Link/LinkPasses.lean). This file
states no goal.

Limits. 1. link_accLaw_home is conditional on the proof-of-work checks. The strategy sends the nonce
0. (Common limit 2.)
2. link_accepts_home proves that one such run exists. Its statement says only that some ρ exists;
how many challenges pass is not its subject (for the search's failure see LinkAccept.lean, limit 1).
In the proofs ρ is built with all proof-of-work bits 0 (passSL_some, LinkPasses.lean: by
inspection), and link_accLaw_home is taken at K := 0 and at one chal, picked by Classical.choice. K
and chal do not occur in the statement.
3. The verifier is the protocol of LinkFrame.lean at the decision of link_yes. No test on the public
files (InScope, protocolDataWellFormed) occurs in it. For the link of homeR b Z see linkFits_at
(Johnson/Goal/Conditions/LinkFitsAt.lean).
Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkAccept
import Johnson.Prover.Link.LinkPasses
import Johnson.Goal.Conditions.LinkAcceptMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open _root_.Run.PQ (SgX)
open _root_.Iop (twoExternalStrings)
open _root_.Desc.K15 (frP linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan)
open OnBytes.Params (recordPlan)
open OnBytes.Prover (AccLaw)
open Johnson.RunOne.StrictW (wqW)
open Johnson.Prover.Link (LCoins keysOf linOf linkNext stratOf link_accLaw accLaw_link_run)

/- Lean compares these by their names. -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **At the honest prover's own input in homeR b Z, the interactive verifier of the link protocol
at the decision of link_yes (Johnson/Prover/Link/LinkJoinF.lean) accepts the explicit honest
prover's run, at all challenges that pass the proof-of-work checks**: AccLaw with the set B empty,
for all K, chal, b, Z, i, q, q', e, e' and C. No premise on Z: that verifier does not depend on Z.
-/
theorem link_accLaw_home (K : ℕ) (chal : ∀ e k, (Fin K → _root_.Iop.Dig 256) → (ckP .two).Ch e k)
    (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (q q' : (homeR b Z).protocol.EncodingRandomness)
    (e e' : (homeR b Z).protocol.OutOfDomainSeed) (C : LCoins) :
    AccLaw
      (linkSkeletonOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs
        fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
          (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V).up
      (wqW (ckP .two) dsFull frS.P.T.a frD.xs
        (fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
          (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V) K chal)
      ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
      ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
      (stratOf (ckP .two) dsFull (linkNext frP frS 97
        (linOf ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
          ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
            (tailWords frS q.2))
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q'.1)))
            (tailWords frS q'.2))) C)) ∅ :=
  link_accLaw K chal _ _ _ _ (accept_met_home b Z i q q' e e').1
    (accept_met_home b Z i q q' e e').2 C

/-- **There are challenges at which that verifier accepts the strategy's own run**, for the same b,
Z, i, q, q', e, e' and C. No premise. -/
theorem link_accepts_home (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index)
    (q q' : (homeR b Z).protocol.EncodingRandomness) (e e' : (homeR b Z).protocol.OutOfDomainSeed) (C : LCoins) :
    ∃ ρ, (linkSkeletonOfRoundData (ckP .two) dsFull frS.P.T.a frD.xs
        fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
          (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V).up.loc.accept
      ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
      ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
      ((stratOf (ckP .two) dsFull (linkNext frP frS 97
      (linOf ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
        ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
          (tailWords frS q.2))
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q'.1)))
          (tailWords frS q'.2))) C)).run ρ).1 = true := by
  obtain ⟨ρ, h1, h2, h3⟩ := accLaw_link_run (ckP .two) dsFull frS.P.T.a frD.xs
    (fun (r : RecFull × RecFull) (V : _root_.Run.PQ.View) =>
      (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf r) V) 0
    (fun e k _ => Classical.choice ((ckP .two).ne e k))
    (linkNext frP frS 97
      (linOf ((homeR b Z).protocol.recOf i q e, (homeR b Z).protocol.recOf i q' e')
        ((homeR b Z).protocol.encodeIndex i q, (homeR b Z).protocol.encodeIndex i q')
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q.1)))
          (tailWords frS q.2))
        (honestPolys frS
          (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef i q'.1)))
          (tailWords frS q'.2))) C)
  exact ⟨ρ, link_accLaw_home 0 _ b Z i q q' e e' C _ h1 h2 h3⟩

end FlashProve

#print axioms FlashProve.link_accLaw_home
#print axioms FlashProve.link_accepts_home
