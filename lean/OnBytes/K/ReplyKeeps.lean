-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyKeeps.lean: the two hypotheses of OnBytes/K/ReplyRun.lean, met for the program's own
links. For proofs only; the program does not import this file.

  `keepsDry_of`, `keepsFailed_of`: a block of the class `L5.Keeps`
    (OnBytes/Tie/Pv/Keeps/KeepsKit.lean) keeps the mark of the dry run and a failed test.
  `check_reply_own`: `check_reply` (OnBytes/K/ReplyRun.lean) for the links as the program builds
    them (`linksOf`, laid into the built links), with no hypothesis of the kind "keeps" left.


-/
import OnBytes.K.ReplyRun
import OnBytes.Tie.Pv.Keeps.KeepsLinks

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Proof OnBytes.Model OnBytes.Model.Stages

theorem keepsDry_of {α : Type} (b : Blk α) [h : L5.Keeps b] : KeepsDry b :=
  fun c x c' hr => (h.out c x c' hr).dry

theorem keepsFailed_of {α : Type} (b : Blk α) [h : L5.Keeps b] : KeepsFailed b := by
  intro c x c' hr hs
  cases hf : c'.failed with
  | some n => rfl
  | none =>
    have := (h.out c x c' hr).mark hf
    rw [this] at hs
    cases hs

instance keeps_firstTail (p : Params.First) (r : LinksResult) : L5.Keeps (firstTail p r) := by
  unfold firstTail
  keeps

/-- Where `Proof.check` says `accepted` on the program's own links. -/
theorem check_reply_own {X : Verify.Public} {cov : Head.Covered} {ls : Array LinkH}
    (hl : Verify.linksOf X cov = .ok ls) (built : Array LinkH) {c : Params.ProofChains}
    {table : Params.TableName} {copy : Nat} {request words : ByteArray} {reply : E}
    {wsLay : WsLay}
    {file : ByteArray}
    (h : Proof.check c table copy request words reply
      (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay) file =
        .accepted) :
    ∃ (rd : ProofRead) (x : FirstEnd) (c' : Ctx) (r : LinksResult) (c1 : Ctx) (got : E),
      (readProof c table copy request words (firstBlock c.first
        (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay) reply)
        file).fromStart = .ok rd ∧
      firstBlock c.first
        (runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay) reply
        (startAt (firstStart c.first) rd.first.view) = .ok (x, c') ∧
      c'.failed = none ∧
      runLinksH (built.zipWith (fun b l => { b with run := l.run }) ls) c.first wsLay
        (startAt (firstStart c.first) rd.first.view) = .ok (r, c1) ∧
      c1.failed = none ∧ r.reply = some got ∧ (got == reply) = true :=
  haveI := L5.keeps_links hl built c.first wsLay
  check_reply (keepsDry_of _) (fun r => keepsFailed_of (firstTail c.first r)) h

end OnBytes.K
