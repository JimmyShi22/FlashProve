-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/WipeS.lean: the closing of a segment (K10): the wiping written for the first chain's
state (`Desc.First.S`, Johnson/Desc/First/State.lean), and the tie of the filler at made-up columns
(Honest/K10/StAtZero.lean) to the description's own fold at any columns, from one premise on each member in front.
Definitions with code; lemmas.

  `singleRowsWithZeroTarget`, `wipeFrame`, `wipeCheck`, `wipeCtx`   the single rows' target set to zero, in a frame, in the state of the
                 calls, in a link's context
  `wipeHere`      at each of the homes in which a frame rests inside a link, the head's front and the finish; in the
                 finish the batched row's target too
  **`wipeS`**      the state wiped: the statement (`wipeSt`), the walk's own state of the calls, and `wipeHere`
  `live_wipe`     the live state of the calls of the wiped state is that of the state, wiped
  **`stAtZero_is`**   every member in front of the closing's place keeps (`Keeps wipeS 0`, Honest/K10/WipeFold.lean);
                 `frontState` returns t at the rounds seen and at some list of columns ⊢ `stAtZero` returns there, and
                 its value is t's statement wiped and t's live group's number

Limits. `Keeps wipeS 0 b` is shown of no member here: a lemma for each kind of member of the first chain stands in
Honest/K10/Wipe/, and `keeps_at_closing` (Wipe/SeatWipe.lean) gathers them. That the fields wiped are all those into
which a column's words go is a reading of the library's texts; if one were missing, `Keeps` would fail at some member,
and no proof of it could be had. No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeFold
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement zeroE SingleRows ReqFrame)
open OnBytes.Model (ChainCheck LinkCtx)
open VerifiableInference.Desc (Block Place OpenedColumn)
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Close (Par)

/-- What a closing has returned, its target set to zero. -/
def singleRowsWithZeroTarget (r : SingleRows) : SingleRows := { r with target := zeroE }

/-- A frame, the target of what the last closing has returned set to zero. -/
def wipeFrame (f : ReqFrame) : ReqFrame := { f with rows := singleRowsWithZeroTarget f.rows }

/-- The state of the calls, its frame wiped. -/
def wipeCheck (c : ChainCheck) : ChainCheck := { c with frame := wipeFrame c.frame }

/-- A link's context, its state of the calls wiped. -/
def wipeCtx (L : LinkCtx) : LinkCtx := { L with check := wipeCheck L.check }

/-- What is held at one kind of place, each frame in it wiped. -/
def wipeHere : Here → Here
  | .between => .between
  | .lay a => .lay { a with L := wipeCtx a.L }
  | .att a => .att { a with L := wipeCtx a.L }
  | .head a => .head { a with fr := wipeFrame a.fr, L := wipeCtx a.L }
  | .fin a => .fin { a with fr := wipeFrame a.fr, row := { a.row with target := zeroE } }
  | .mem a => .mem a

/-- **The first chain's state, wiped.** -/
def wipeS (s : S) : S :=
  { s with st := wipeSt s.st, check := wipeCheck s.check, here := wipeHere s.here }

/-- The live state of the calls of the wiped state. -/
theorem live_wipe (s : S) : (wipeS s).live = wipeCheck s.live := by
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | between => rfl
  | lay a => rfl
  | att a => rfl
  | head a =>
    unfold S.live S.link? wipeS wipeHere
    dsimp only
    cases a.opened <;> rfl
  | fin a => rfl
  | mem a => rfl

/-- Two states that are one once wiped have one live group's number. -/
theorem group_of_wipe {s t : S} (h : wipeS s = wipeS t) : s.live.frame.group = t.live.frame.group := by
  have e := congrArg (fun z : S => z.live.frame.group) h
  simp only [live_wipe] at e
  exact e

/-- **The filler's value**, from one premise on each member in front. -/
theorem stAtZero_is {Cl Xi : Type} (bs : List (Block S Cl)) (start : Xi → S) (x : Xi) (P : Par) (seen : Seen)
    (front : List Fmt.Drawn)
    (hk : ∀ b ∈ bs.takeWhile (·.place != closePlace P), Keeps wipeS 0 b) {cols : List OpenedColumn} {t : S}
    (h : frontState 0 bs (start x) (closePlace P) seen.rounds cols = .ok t) :
    stAtZero bs start x P seen front = .ok (wipeSt t.st, t.live.frame.group) := by
  obtain ⟨t0, h0, hw⟩ := front_zero wipeS 0 bs (closePlace P) hk h
  unfold stAtZero stAtZeroBy
  rw [h0]
  have e1 : wipeSt t0.st = wipeSt t.st := congrArg (fun z : S => z.st) hw
  show Except.ok (wipeSt t0.st, t0.live.frame.group) = _
  rw [e1, group_of_wipe hw]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.singleRowsWithZeroTarget
#print axioms ProofFile.Honest.K10.wipeFrame
#print axioms ProofFile.Honest.K10.wipeCheck
#print axioms ProofFile.Honest.K10.wipeCtx
#print axioms ProofFile.Honest.K10.wipeHere
#print axioms ProofFile.Honest.K10.wipeS
#print axioms ProofFile.Honest.K10.live_wipe
#print axioms ProofFile.Honest.K10.group_of_wipe
#print axioms ProofFile.Honest.K10.stAtZero_is
