-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/LinkLaidHashedAccepted.lean: wherever a link proof in the hashed scheme's key is
produced, the link's interactive verifier accepts the transcript with which the compiled link prover
returned it.

Summary. AtFullSide/E2E/LinkLaidAccepted.lean is about the interactive link protocol. This file
proves that the link's interactive verifier accepts the explicit link prover's run also at the
challenges that hashing gives, for `laidAt` (that prover with two placeholder provers). It holds for
public files in scope with a live description, for all oracle functions and all coins: there is no
probability in it. One transcript ties five facts together: the compiled prover returned it, the
proof holds its plain messages, the verifier's own hash chain on the proof's fields reproduces its
verifier messages, the prover did not abort, and the interactive verifier accepts it. The main
limit: it is the interactive verifier that accepts, not the compiled one.

Main results, at the parameters with an all-zero digest.
  `laid_hashed_accepted` (`LinkHashedAcceptedAt R a`): for public files Z in scope with a live
    description: for every index, all oracle functions g, all coins of the committer and every copy
    whose link proof π is produced, there is a transcript τ such that:
    1. the compiled link prover, on the scheme's own arguments, under g, returns (π, τ);
    2. `PlainAt`: π's plain messages are τ's; τ's verifier messages pass all proof-of-work tests;
    and τ is the run of the strategy that the prover plays, for these verifier messages, except for
    the nonces, which are numbers within the search limit;
    3. the prover does not abort at τ's verifier messages;
    4. the verifier's own hash chain, run under g on π's own fields (its salt, its request's digest,
    its roots, its plain messages), yields τ's verifier messages;
    5. the link's interactive verifier accepts τ, for both tables' OOD samples and the link prover's
    external strings.
    Clauses 1 to 4 are the conclusion of `link_hashed` (E2E/StringsPlain.lean), verbatim, for these
    parameters.
  `laid_hashed_accepted_zFull`, `laid_hashed_accepted_zGap`: the same at `VerifierAndGoals.storedPublicFiles` and
    `VerifierAndGoals.zGap`: no premise on the public files is left.

How. `link_hashed` (E2E/StringsPlain.lean), the third clause of `laid_accepted`
(AtFullSide/E2E/LinkLaidAccepted.lean) and `fits_home` (E2E/LinkLaidPrivacy.lean).

Terms: E2E/HidingTerms.lean.

Limits.
- That the compiled verifier accepts the proof is not proved, and no lemma that ends in its
  acceptance can be applied to `laidAt` (the header of E2E/LinkLaidPrivacy.lean says why).
- It speaks only where the link proof is produced. How often that is, is another statement
  (`LinkLaidStrings`, E2E/LinkLaidPrivacy.lean), on the scheme's run; this one is for all g and all
  coins. No theorem joins the two. The search limits are free parameters here: with limits of 0 a
  link proof is hardly ever produced (not proved in Lean: a hand count of the tests' bits).
- One of three protocols: nothing on the first table's proof and the sessions' proofs, whose provers
  are placeholders.
- It is stated at `homeR b Z`, the input at one fixed digest. That `VerifierAndGoals.verify` is ever called at
  this input is not proved (the header of E2E/LinkLaidPrivacy.lean).
- All limits of the files that are used hold.

Definitions and helper lemmas.
  `LinkHashedAcceptedAt R a`: the statement, for arbitrary R and arbitrary parameters a.
  `linkHashedAccepted_of`: it holds where the four clauses on the link (`LinkAcceptedAt`) hold with
    no verifier message excluded, for Yes := True and no seed excluded; the link prover never
    aborts; there is an instance; and the wires fit (`WiresFit`: its clause "few trees a round" for
    the link is what is used).

This file lies in the side library AtFullSide, which is built with a larger thread stack
(lake build AtFullSide).


-/
import AtFullSide.E2E.LinkLaidAccepted
import E2E.LinkLaidAllAtOnce
import E2E.StringsPlain
import Johnson.LinkSim.AtHome.TwoViews

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.LinkLaid
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.Shown
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles storedPublicFiles zGap)
open FlashProve (protocolDataWellFormed homeR)
open AtPublicFiles.AtWritten (open_zFull open_zGap)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-- **Where a link proof π in the key is produced: the compiled link prover returned it with a
transcript τ; π's plain messages are τ's; τ is the played strategy's own run for τ's verifier
messages, except for the nonces; the verifier's own hash chain on π's fields yields these verifier
messages; and the link's interactive verifier accepts τ**, for arbitrary R. -/
def LinkHashedAcceptedAt (R : InnerCompilerInput) (a : AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits) : Prop :=
  ∀ (g : Fam (typedOracleFamily 256 R.queryLayout.K (typedOracleCarrier R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits))) (i : R.Index)
    (c : DrawC 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits a.side.KT a.side.KL) (j : ℕ)
    (e : DrawCopy 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits a.side.KL), c.copies[j]? = some e →
    ∀ l : Dig 256 × R.protocol.Rec × Option (OneProtocolProof 256 (batLC R.protocol R.linkRoundSplits)),
      ((commitAt R.queryLayout R.seedQueries R.answerCode a.side i c).det g).1.links[j]? = some l →
      ∀ π : OneProtocolProof 256 (batLC R.protocol R.linkRoundSplits), l.2.2 = some π →
        ∃ τ : Tr (batLC R.protocol R.linkRoundSplits).loc.shape,
          (proveLA R.queryLayout R.answerCode
            (fun k => if k = 0 then (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).tree else (tabG R.queryLayout R.seedQueries
                                   a.side g i e.r e.s).tree)
            (a.side.dressL (a.side.rvL e.κ) e.co) a.side.capL (tabG R.queryLayout R.seedQueries a.side g i c.r
                c.s).tree.root
            (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).tree.root (R.protocol.recOf i c.r (tabG R.queryLayout R.seedQueries a.side g i
                                          c.r c.s).seed)
            (R.protocol.recOf i e.r (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).seed) (R.protocol.encodeIndex i c.r, R.protocol.encodeIndex i e.r)
            (a.side.st.Lk i (c.r, (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed) (e.r, (tabG R.queryLayout R.seedQueries
                                   a.side g i e.r e.s).seed)
              e.κ)).det g = .ok (π, τ) ∧
          PlainAt (batLC R.protocol R.linkRoundSplits) (wLC R.queryLayout)
            (a.side.st.Lk i (c.r, (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed) (e.r, (tabG R.queryLayout R.seedQueries
                                   a.side g i e.r e.s).seed) e.κ)
            a.side.capL π τ ∧
          a.side.st.stopL i (c.r, (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed) (e.r, (tabG R.queryLayout R.seedQueries
                                 a.side g i e.r e.s).seed)
            τ.rho = false ∧
          (∃ Rt ph, TypedOracleCompiler.Run.chainF g _root_.Compile.Tag.link
            (cmsLA R.answerCode (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).tree.root (tabG R.queryLayout R.seedQueries a.side g i e.r
                                           e.s).tree.root
              (R.protocol.recOf i c.r (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed).2
              (R.protocol.recOf i e.r (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).seed).2) none π.salt π.rtreq
            (batLC R.protocol R.linkRoundSplits).loc.shape (batLC R.protocol R.linkRoundSplits).ann (wLC R.queryLayout).sh id 0 .first π.roots
                π.plains =
              some (τ.rho, Rt, ph)) ∧
          (batLC R.protocol R.linkRoundSplits).loc.accept
            (R.protocol.recOf i c.r (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed,
              R.protocol.recOf i e.r (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).seed)
            (a.Hs.Lk.ext (i, (c.r, (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed),
              (e.r, (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).seed))) τ = true

theorem linkHashedAccepted_of (R : InnerCompilerInput) (a : AtRecs 256 R.protocol R.LeafBody R.offlineRoundSplits R.linkRoundSplits)
    (hA : LinkAcceptedAt R a.Hs (Falls.none a.Hs) (fun _ _ => True) fun _ _ => ∅)
    (hw : ∀ w x, a.Hs.Lk.withheld w x = ∅) (hx : Nonempty R.Instance) (hW : WiresFit R.queryLayout R.answerCode) :
    LinkHashedAcceptedAt R a := by
  intro g i c j e hj l hl π hπ
  obtain ⟨x₀⟩ := hx
  obtain ⟨τ, hτ, hp, hstop, hch⟩ := link_hashed R.queryLayout R.seedQueries R.answerCode a.side g hW i c j e hj l hl π hπ
  have hacc := hA.2.2.1 i x₀ c.r (tabG R.queryLayout R.seedQueries a.side g i c.r c.s).seed e.r
    (tabG R.queryLayout R.seedQueries a.side g i e.r e.s).seed e.κ trivial (Set.notMem_empty _) (Set.notMem_empty _)
  refine ⟨τ, hτ, hp, hstop, hch, hacc τ hp.2.1 hp.puts fun hm => ?_⟩
  rcases (Set.mem_union _ _ _).1 hm with h | h
  · rw [hw] at h
    exact Set.notMem_empty _ h
  · exact Set.notMem_empty _ h

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **At `homeR b Z` and `laidAt`**, for public files Z in scope with a live description. -/
theorem laid_hashed_accepted (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) :
    LinkHashedAcceptedAt (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E) :=
  linkHashedAccepted_of (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
    (laid_accepted b Z scope live b₀ M ℓ ℓr capT capL capB E (fun _ _ => True) fun _ _ => ∅)
    (fun w x => home_withheld b Z w x) (instance_home b Z) (fits_home b Z).2

theorem laid_hashed_accepted_zFull (b₀ : (homeR b storedPublicFiles).LeafBody) (M ℓ ℓr : ℕ)
    (capT capL capB : ℕ → ℕ) (E : BitsE b storedPublicFiles b₀ M ℓ ℓr capT capL capB) :
    LinkHashedAcceptedAt (homeR b storedPublicFiles) (laidAt b storedPublicFiles b₀ M ℓ ℓr capT capL capB E) :=
  laid_hashed_accepted b storedPublicFiles open_zFull.1 open_zFull.2 b₀ M ℓ ℓr capT capL capB E

theorem laid_hashed_accepted_zGap (b₀ : (homeR b zGap).LeafBody) (M ℓ ℓr : ℕ)
    (capT capL capB : ℕ → ℕ) (E : BitsE b zGap b₀ M ℓ ℓr capT capL capB) :
    LinkHashedAcceptedAt (homeR b zGap) (laidAt b zGap b₀ M ℓ ℓr capT capL capB E) :=
  laid_hashed_accepted b zGap open_zGap.1 open_zGap.2 b₀ M ℓ ℓr capT capL capB E

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.linkHashedAccepted_of
#print axioms AtPublicFiles.LinkLaid.laid_hashed_accepted
#print axioms AtPublicFiles.LinkLaid.laid_hashed_accepted_zFull
#print axioms AtPublicFiles.LinkLaid.laid_hashed_accepted_zGap
