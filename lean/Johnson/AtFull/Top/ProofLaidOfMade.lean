-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Top/ProofLaidOfMade.lean: two names and two small laws for the statements on the
maker of the proof file's laid description (`FlashProve.theProofLaid`) at the full size.

Main names.
* `ZqM pol KL m`: the value that the proof file's public part takes where the planner's answer m has
  the written parts: the value in `pubPlain_of_made` (Johnson/AtFull/Pub/PubOfMade.lean). Its
  declared rounds, trees, depth, cuts and first state are written values; the parameter file, the
  scale file and m are letters.
* `FW o pol KL m A B c`: the proof file's description at `ZqM`, over a first chain c and two later
  seats A, B.
* `sends_of_madeAt`: what `Key.madeAt` returns holds the last three of the sendings that it made.
* `proof_of_free`: where the planner's four free parts are the written ones, the proof file's three
  lists of sendings are the written ones. By the closed `sendsWhole_all`
  (Johnson/AtFull/Sends/SendsWhole.lean).

The statement that the maker returns is `proofLaid_of_desc`
(Johnson/AtFull/Top/ProofLaidOfDesc.lean). What it asks is named, premise by premise, in
Johnson/AtFull/Top/ProofLaidOfLedgers.lean.

A second text. `ZqM` stands a second time, as ZqW, in a working file of this project, which
is not in this repository (sha256 a113f722e45f1aa5e8ce851c1d7884799b1103e9a9620b58ce2500c5552bd934)
and is not imported here.

Limits. Definitions and two laws. That the planner returns at any files, or that its answer has the
written parts, is not shown in this file. No return of `theProofLaid` is shown in this file. That
the premises of `proofLaid_of_desc` can be met together is shown at storedPublicFiles alone: `proofLaid_zFull`
(Johnson/AtFull/Top/LiveAtZFull.lean), under two closed facts on the layout file whose proofs lie in
the side library. No example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap, whose own Limits say what they are worth. No
soundness is claimed.

-/
import Johnson.AtFull.Top.ProofLaidOfLedgers
import Johnson.AtFull.Pub.PubOfMade
import Johnson.Desc.Key.NoCfgLive
import Johnson.Goal.Files.ScopeExample
import Johnson.AtFull.ProofRows.WrittenProof
import Johnson.AtFull.Top.RowFourteenThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open Johnson.AtFull.Cut (cutWritten)
open Johnson.AtFull.Pub (DW toldW)

/-- The public part's value: pubPlain_of_made's. -/
abbrev ZqM (pol KL : ByteArray) (m : Made) : Pub :=
  pubOfParts plainStarts pol KL (ProofFile.Law.blankM m) DW toldW 32 cutWritten
    (S.firstRecord proofSizedFull.codes proofSizedFull.request layoutFull)

/-- The proof file's description at the written public part. -/
abbrev FW (o : SecondHashFunctionArgument) (pol KL : ByteArray) (m : Made) (A : SharedSeat) (B : SecondSeat)
    (c : Chain S Cl) : FileDescription Inst :=
  fileDescBy o pureRoad.links (ZqM pol KL m) A B (fun s => s) (startS (ZqM pol KL m)) c

/-- What the key file's planner returns holds the last three of the sendings that it made. -/
theorem sends_of_madeAt {X : OnBytes.Model.Verify.Public} {lay c : ByteArray} {m : Made}
    (h : madeAt X lay c = .ok m) :
    ∃ k0 k1 k2 e, Johnson.G.sendsFrom m.p.chains.made =
      .ok [k0, k1, k2, e, m.proof.1, m.proof.2.1, m.proof.2.2] := by
  unfold madeAt at h
  obtain ⟨ch, -, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨b, -, h⟩ := OnBytes.Params.exc_bind h
  obtain ⟨l, h3, h⟩ := OnBytes.Params.exc_bind h
  split at h
  · obtain rfl : _ = m := Except.ok.inj h
    exact ⟨_, _, _, _, h3⟩
  · cases h

/-- **Where the planner's four free parts are the written ones, the proof file's three lists of
sendings are the written ones**: by the closed sendsWhole_all. -/
theorem proof_of_free {X : OnBytes.Model.Verify.Public} {lay c : ByteArray} {m : Made}
    (hm : madeAt X lay c = .ok m) (e1 : MadeFree.freeOf m.p.chains.made = writtenMade) :
    m.proof = proofSendsFull := by
  obtain ⟨En, hA⟩ := Johnson.AtFull.Sends.sendsWhole_all
  obtain ⟨k0, k1, k2, e, hB⟩ := sends_of_madeAt hm
  have hL := Except.ok.inj (hB.symm.trans (hA _ e1))
  simp only [List.cons.injEq, and_true] at hL
  obtain ⟨-, -, -, -, p0, p1, p2⟩ := hL
  exact Prod.ext p0 (Prod.ext p1 p2)

end AtFull.Top

#print axioms AtFull.Top.sends_of_madeAt
#print axioms AtFull.Top.proof_of_free
