-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ReplyRun.lean: the token that the prover names for the reply, against the caller's reply:
the step on runs, as far as the first chain's own block. For proofs only; the program does
not import this file.

A named test on values (`Blk.check`, OnBytes/Iop/Ground.lean) does not stop a run: where it is false
it lays its name into the field `failed` of what the verifier holds, and the run on a view is
refused at its end if that field is not empty. So from a yes to "the test was true" one needs that
no later step empties the field, and that no earlier step has switched the dry run on.
  `KeepsFailed b`: a run of b that starts with a failed test ends with one.
  `KeepsDry b`: a run of b leaves the mark of the dry run as it was.
  `firstTail p r`: what `Proof.firstBlock` (OnBytes/Proof/File.lean) does behind its comparison of
    the reply.
  `firstBlock_reply`: if the caller's block `links` keeps the mark of the dry run, and `firstTail`
    keeps a failed test: a run of `firstBlock p links reply` on a view that ends with no failed test
    has got a reply from `links`, and that reply is equal to `reply`.
  `check_reply`: so, under the same two hypotheses, where `Proof.check` says `accepted`: with the
    proof file as read, and the context made of its own first view (`startAt`), named.
The two hypotheses are not proved here. They are named so that whoever proves that the session's
verifier says yes finds them; OnBytes/K/ReplyKeeps.lean meets them for the program's own links.
What is not claimed: that the reply which `links` returns is the first plain scalar of the head's
link; that the head's check is given that same list; that the head's routine runs at the window at
which the statement's positions were made. OnBytes/K/ReplyRoot.lean goes on from here.


-/
import OnBytes.K.ReplyToken
import OnBytes.Proof.File

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Proof

/-- A run of b that starts with a failed test ends with one. -/
def KeepsFailed {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b c = .ok (x, c') → c.failed.isSome = true → c'.failed.isSome = true

/-- A run of b leaves the mark of the dry run as it was. -/
def KeepsDry {α : Type} (b : Blk α) : Prop :=
  ∀ c x c', b c = .ok (x, c') → c'.ch.dry = c.ch.dry

/-- The context from which the program runs a block on a view: the record of `Blk.runNamed`
(OnBytes/Iop/Ground.lean) at a run that is not dry, the view's rounds and its opened columns. It is
written here so that this file stands on the library alone; that it is `TieK.startCtx`
(OnBytes/TieK/RunAt.lean) and `Cut.start` (OnBytes/Cut/Run.lean) is shown in OnBytes/Cut/Same.lean
[not in this library; so here read: not proved in this library].
-/
def startAt (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

/-- What `firstBlock` does behind its comparison of the reply. -/
def firstTail (p : Params.First) (r : LinksResult) : Blk FirstEnd := do
  Blk.must (r.pending.length == p.pendingRows)
  let lin ← memberFirstVerify p.lin r.indexMasks r.pending
  firstEnd lin

/-- A run of the first chain's block on a view that ends with no failed test. -/
theorem firstBlock_reply {p : Params.First} {links : Blk LinksResult} {reply : E}
    (hl : KeepsDry links) (ht : ∀ r, KeepsFailed (firstTail p r)) {c c' : Ctx} {x : FirstEnd}
    (h : firstBlock p links reply c = .ok (x, c')) (hd : c.ch.dry = false)
    (hf : c'.failed = none) :
    ∃ r c1 got, links c = .ok (r, c1) ∧ c1.failed = none ∧ r.reply = some got ∧
      (got == reply) = true := by
  have h' : (do
      let r ← links
      let got ← Blk.get r.reply
      Blk.check replyCheck (got == reply)
      firstTail p r : Blk FirstEnd) c = .ok (x, c') := h
  simp only [bind, StateT.bind, Except.bind] at h'
  cases h1 : links c with
  | error e =>
    rw [h1] at h'
    cases h'
  | ok v =>
    obtain ⟨r, c1⟩ := v
    rw [h1] at h'
    dsimp only at h'
    cases h2 : r.reply with
    | none =>
      simp only [Blk.get, h2] at h'
      cases h'
    | some got =>
      simp only [Blk.get, h2] at h'
      have hd1 : c1.ch.dry = false := (hl c r c1 h1).trans hd
      unfold Blk.check at h'
      have hs : ¬c1.failed.isSome = true := by
        intro hs
        simp only [hs, Bool.or_true, if_true] at h'
        have := ht r c1 x c' h' hs
        rw [hf] at this
        cases this
      have hs' : c1.failed = none := by
        cases hc : c1.failed with
        | none => rfl
        | some n =>
          rw [hc] at hs
          exact absurd rfl hs
      refine ⟨r, c1, got, rfl, hs', h2, ?_⟩
      by_cases hb : (got == reply) = true
      · exact hb
      · exfalso
        simp only [hb, hd1, hs, Bool.or_false, Bool.false_eq_true, if_false] at h'
        have := ht r _ x c' h' rfl
        rw [hf] at this
        cases this

/-- Where `Proof.check` says `accepted`: the proof file was read as rd; the first chain's block has
run from the context made of rd's own first view and has ended with no failed test; from that same
context `links` has returned a reply, and it is equal to the caller's. -/
theorem check_reply {c : Params.ProofChains} {table : Params.TableName} {copy : Nat}
    {request words : ByteArray} {reply : E} {links : Blk LinksResult} {file : ByteArray}
    (hl : KeepsDry links) (ht : ∀ r, KeepsFailed (firstTail c.first r))
    (h : Proof.check c table copy request words reply links file = .accepted) :
    ∃ (rd : ProofRead) (x : FirstEnd) (c' : Ctx) (r : LinksResult) (c1 : Ctx) (got : E),
      (readProof c table copy request words (firstBlock c.first links reply) file).fromStart =
        .ok rd ∧
      firstBlock c.first links reply (startAt (firstStart c.first) rd.first.view) = .ok (x, c') ∧
      c'.failed = none ∧
      links (startAt (firstStart c.first) rd.first.view) = .ok (r, c1) ∧ c1.failed = none ∧
      r.reply = some got ∧ (got == reply) = true := by
  unfold Proof.check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i rd hrd
    split at h
    · cases h
    · rename_i hn
      rw [proofRefusal_eq] at hn
      split at hn
      · cases hn
      · rename_i real hj
        unfold judge at hj
        split at hj
        · rename_i a ha
          unfold Blk.runOn at ha
          split at ha
          · cases ha
          · rename_i a' ctx hr
            split at ha
            · cases ha
            · rename_i hfail
              unfold Blk.runNamed at hr
              split at hr
              · have hr' : firstBlock c.first links reply
                    (startAt (firstStart c.first) rd.first.view) = .ok (a', ctx) := hr
                obtain ⟨r, c1, got, g1, g0, g2, g3⟩ := firstBlock_reply hl ht hr' rfl hfail
                exact ⟨rd, a', ctx, r, c1, got, hrd, hr', hfail, g1, g0, g2, g3⟩
              · cases hr
        · cases hj

end OnBytes.K
