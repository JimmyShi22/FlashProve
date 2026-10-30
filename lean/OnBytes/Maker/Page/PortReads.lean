-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/PortReads.lean: what the yes of the verifier program's checks says of its own
reading of the key file and of the proof file: the reader has returned, and the decision has said
yes. The hypothesis is `K.PortYesAt`, not the exit code 0: the step from the exit code is
`main_zero_port` (OnBytes/K/Top.lean), which gives the two tables under "there is".

`K.PortYesAt F id table further` (OnBytes/K/Top.lean) holds the yes of `Key.check` on the key file
and of `Proof.check` on the proof file, at the chains that the planner gives for the three public
files. OnBytes/Maker/OfThreeChains.lean opens a check's yes into a reading that returns and a
decision that says yes. This file puts the two together.

Main theorems.
  `port_key_check`: the yes of `Key.check`, at the planner's chains.
  `port_key_reads`: the table's reading, the key file's reading and the decision's yes.
  `port_proof_reads`: the proof file's reading and the decision's yes, at the block that the program
    makes of the request, the reply and the links.
Each letter under "there is" stands with the equation that makes it from the files.

What is not claimed. That these readings are those of the fixed reading of
OnBytes/TieK/ReadThree.lean. Nothing on soundness.


-/
import OnBytes.Maker.OfThreeChains
import OnBytes.TieK.PortCommon

set_option autoImplicit false

namespace OnBytes.Maker.Page

/-- **The yes of the key file's check**, at the planner's chains. -/
theorem port_key_check {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) :
    ∃ p, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.check p.chains.key F.key = .ok table := by
  obtain ⟨_, p, _, -, -, -, -, -, -, -, -, -, -, hp, -, -, hk, -⟩ := h
  exact ⟨p, hp, hk⟩

/-- **The key file: the program's reader has returned and its decision has said yes.** -/
theorem port_key_reads {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) :
    ∃ p j r, Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg F.key =
        .ok (table, j) ∧
      (Key.readKey p.chains.key table F.key j).fromStart = .ok r ∧
      Key.keyRefusal p.chains.key table r = none := by
  obtain ⟨p, hp, hk⟩ := port_key_check h
  obtain ⟨j, r, h1, h2, h3⟩ := key_check_reads _ _ _ hk
  exact ⟨p, j, r, hp, h1, h2, h3⟩

/-- **The proof file: the program's reader has returned and its decision has said yes.** -/
theorem port_proof_reads {F : K.Files} {id : String} {table further : Params.TableName}
    (h : K.PortYesAt F id table further) :
    ∃ p so cov item links r,
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      Model.Head.stFromCall (Model.Verify.words32 F.request) (Model.Verify.words32 F.y) p.X.T =
        .ok so ∧
      Model.Head.coveredOf so p.X.T p.X.P.h.V = .ok cov ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      Model.Verify.linksOf p.X cov = .ok links ∧
      (Proof.readProof p.chains.proof further F.entry item F.request
        (Proof.firstBlock p.chains.proof.first
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y)) F.proof).fromStart = .ok r ∧
      Proof.proofRefusal p.chains.proof further
        (Proof.firstBlock p.chains.proof.first
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y)) r = none := by
  obtain ⟨p, so, cov, item, links, hp, h1, h2, h3, h4, hc, -⟩ := TieK.port_common h
  obtain ⟨r, g1, g2⟩ := proof_check_reads _ _ _ _ _ _ _ _ hc
  exact ⟨p, so, cov, item, links, r, hp, h1, h2, h3, h4, g1, g2⟩

end OnBytes.Maker.Page
