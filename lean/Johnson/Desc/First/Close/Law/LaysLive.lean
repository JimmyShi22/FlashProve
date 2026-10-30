-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LaysLive.lean: into which copy of the state of the calls the closing of
a link lays its open claim: the live one. One definition, statements and proofs.

Inside a link the chain's record (`S`, Johnson/Desc/First/State.lean) holds the state of the calls
twice: the walk's own copy `check`, which is stale there, and the link's copy, which is live.
`S.live` reads the live one and `S.putLive` writes it. The claim that a closing leaves open is taken
up behind the link, so it matters which of the two copies holds it. `closeFrame_lays` (Lays.lean,
beside this file) speaks of a frame as plain data. Here it is said of the record.
  `S.live_putLive`: what has been written into the live copy is read off it.
  `S.check_putLive`: where a link is open, writing the live copy leaves the walk's own copy as it
    was.
  `Close.atLive ow P`: the closing's block (`kind P`, Johnson/Desc/First/Close/Kind.lean) at the
    record: its part is read off the live copy and written back into that one. ow: how the rows owed
    are read.
  `Close.atLive_lays`: if that block says yes: the live copy behind is the live copy in front but
    for four fields of its frame: `rows`, which holds the open claim; `mask` := none; `link` one
    more; `next` := "the first message of a link". Where a link is open the walk's own copy is as it
    was.

Limits. Of the closing's block alone: the blocks that stand beside it in one place (the one equation
in front; the marking of the segment's book-keeping behind) are not treated. What the block turns of
the statement and of the rows owed is not said. One direction. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Lays
import Johnson.Desc.First.Close.Kind
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open OnBytes OnBytes.Model

/-- What has been written into the live copy is read off it. -/
theorem S.live_putLive (s : S) (c : ChainCheck) : (s.putLive c).live = c := by
  unfold S.putLive S.live S.link? S.putLink
  cases hh : s.here with
  | lay a => simp
  | att a => simp
  | head a =>
    by_cases ho : a.opened = true
    · simp [ho]
    · simp [ho]
  | _ => simp

/-- Where a link is open, writing the live copy leaves the walk's own copy as it was. -/
theorem S.check_putLive (s : S) (c : ChainCheck) (L : LinkCtx) (h : s.link? = some L) :
    (s.putLive c).check = s.check := by
  unfold S.putLive
  rw [h]
  unfold S.putLink
  dsimp only
  split
  · rfl
  · rfl
  · split <;> rfl
  · rfl

namespace Close

variable {Cl : Type}

/-- K10's block at the chain's record, as it is seated: its part of the record is read off the live
state of the calls and written back into that one. ow: how the rows owed are read. -/
def atLive (ow : S → Option Nat) (P : Par) : Block S Cl :=
  (kind P).lift (fun s => ⟨ow s, s.live.frame, s.st⟩)
    (fun s r => { s.putLive { s.live with frame := r.frame } with st := r.st, rowsOwed := r.owed })

/-- **K10's BLOCK LAYS ITS OPEN CLAIM INTO THE FIELD `rows` OF THE LIVE COPY's FRAME, AND INTO NO
OTHER FIELD OF THE STATE OF THE CALLS.** -/
theorem atLive_lays (ow : S → Option Nat) (P : Par) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (atLive (Cl := Cl) ow P).decide s rs gs = .ok s') :
    s'.live = { s.live with frame :=
      { s.live.frame with rows := s'.live.frame.rows, mask := none,
                          link := s.live.frame.link + 1, next := .first } } ∧
    (∀ L, s.link? = some L → s'.check = s.check) := by
  have h1 : ((closeFrame (ow s) s.live.frame s.st (entries P) rs).map
      fun x => (⟨none, x.1, x.2⟩ : Rec)).map
        (fun r => { s.putLive { s.live with frame := r.frame } with
          st := r.st, rowsOwed := r.owed }) = .ok s' := h
  cases hc : closeFrame (ow s) s.live.frame s.st (entries P) rs with
  | error e => rw [hc] at h1; cases h1
  | ok x =>
    rw [hc] at h1
    have h2 : ({ s.putLive { s.live with frame := x.1 } with st := x.2, rowsOwed := none } : S) =
        s' := Except.ok.inj h1
    have hl : s'.live = { s.live with frame := x.1 } := by
      rw [← h2]
      exact S.live_putLive s _
    have hx := closeFrame_rows (f' := x.1) (S' := x.2) hc
    refine ⟨?_, fun L hL => ?_⟩
    · rw [hl]
      exact congrArg (fun f => ({ s.live with frame := f } : ChainCheck)) hx
    · rw [← h2]
      exact S.check_putLive s _ L hL

end Close

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.live_putLive
#print axioms VerifiableInference.Desc.First.Close.atLive_lays
