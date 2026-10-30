-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/CallInst.lean: the typed instance of a call of the shipped Lean verifier: from
the program's yes to one instance at which the flat description's block is the program's block,
the proof file was read and judged at that block, and the bytes of the item `request` are the
program's.

The makers of a proof file's protocol take the first chain's block and the bytes of the item
`request` as functions of a typed instance. Three files say what these are at the instance that is
built from a call's request file and reply file: Johnson/Flat/InsOf.lean (the instance is there, and
the words that say it are the files' words), Johnson/Maker/Page/BlockFlat.lean (at such an instance
the flat description's block is the program's) and Johnson/Maker/Page/ReqIns.lean (at the built
instance with the reply wiped the bytes are the program's item). This file joins them at ONE
instance: `insOf` is a function, so the three speak of the same i.

Main name:
  `inst_port`: from the program's yes (`K.PortYesAt`), at the sizes P that the parameter file
    states: there is an instance i with `insOf P (K.stmOf F o) = some i`; the words that say i are
    the words of the call's request file and reply file, and i holds the call's five files
    (`HoldsPub.pub`, Johnson/Maker/Page/ReqPub.lean); all clauses of
    `yes_block_flat` at i, among them `(pubOf p P hV).block i = firstBlockOf p links so.y` and the
    flat record of the three chains at that block; and `reqX (withoutReply hV i) = item`, at the
    item of these clauses.
The instance is a letter of its own: nothing is said of the fixed instance at which a description's
dry runs are made.
What is asked, by name: hp: the program's yes. hP: the sizes. hV: the vocabulary is not empty. That
window and vocabulary are within a word's range is had from hP and the plan (`sizesAt_planned`,
Johnson/Flat/SizesPlanned.lean).

Limits: nothing where `sizesAt` refuses the parameter file (hP): by the Limits of
Johnson/Flat/ItemOf.lean the exit code 0 can occur there.
Nothing on a dry run at another instance than the call's. One direction only. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Maker.Page.BlockFlat
import Johnson.Maker.Page.ReqIns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes OnBytes.Proof OnBytes.TieK OnBytes.Flat Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- **The typed instance of a call.** -/
theorem inst_port {F : K.Files} {id : String} {table further : OnBytes.Params.TableName}
    (hp : K.PortYesAt F id table further) (o : Options) {P : Params}
    (hP : sizesAt F.pol = .ok P) (hV : 0 < P.V) :
    ∃ i : Instance' P, ∃ p so cov item links j d real real2,
      insOf P (K.stmOf F o) = some i ∧
      requestWordsOf i = words32 F.request ∧ replyWordsOf i = words32 F.y ∧
      (holdsIns hV F.pol F.lay F.KL).pub i = ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ ∧
      Model.Verify.planned F.pol F.KL (some F.lay) = .ok p ∧
      CallFacts p (requestWordsOf i) (replyWordsOf i) so cov links ∧
      (pubOf p P hV).block i = firstBlockOf p links so.y ∧
      Proof.requestItem F.pol F.KL F.request = some item ∧
      (holdsIns hV F.pol F.lay F.KL).reqX (withoutReply hV i) = item ∧
      readProofHead p.chains.proof.first.given.plan.field F.proof = .ok (F.entry, j) ∧
      readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof = some (further, d) ∧
      p.chains.proof.first.describe further F.entry item F.request d.rounds1 = some d.S1 ∧
      ThreeChains (tailPublic p.chains.proof further) ((pubOf p P hV).block i)
        (firstStart p.chains.proof.first) F.proof j d.rounds1 d.dry d.S1 d.r d.seal1 d.seal2
        d.rounds2 d.dry2 d.S2 d.rounds3 d.S3 real real2 ∧
      SlotFacts (tailPublic p.chains.proof further).binding
        (tailPublic p.chains.proof further).shared.given.cfg d.seal1 F.proof d.r.first.next
        d.r.place d.salt d.path ∧
      d.copy = F.entry := by
  obtain ⟨p₀, i, hp₀, a, _, hi, hR, hQ, hre, hy⟩ := insOf_port hp o hP
  obtain ⟨-, -, hT, hV'⟩ := sizesAt_planned hP hp₀
  obtain ⟨i', item', hi', hpub, hit', hreq⟩ := req_port hV hp o hP
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  obtain ⟨so, cov, item, links, j, d, real, real2, hf, hb, h3, hh, hd, hs, T, sf, hc⟩ :=
    yes_block_flat hp hp₀ P hV i a hT hV' hR hQ hre hy
  obtain rfl : item = item' := Option.some.inj (h3.symm.trans hit')
  exact ⟨i, p₀, so, cov, item, links, j, d, real, real2, hi, hR, hQ, hpub, hp₀, hf, hb, h3, hreq,
    hh, hd, hs, T, sf, hc⟩

end Johnson.Session
