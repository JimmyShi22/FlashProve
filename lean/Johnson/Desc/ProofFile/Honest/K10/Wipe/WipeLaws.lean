-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/WipeLaws.lean: how the functions of Johnson/Desc/First/State.lean behave at a
wiped state. One definition with code (`wipeD`); the rest are theorems.

Words. The wiped state of the first chain (`wipeS`, Honest/K10/WipeS.lean) is the state with these targets set to zero:
those of the statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched
row; the rows on the table (the pile `out.pending`, and the claim at the chain's end) keep theirs. The other wipings
named here (`wipeSt`, `wipeCheck`, `wipeCtx`, `wipeFrame`, `wipeHere`) do the same to a part of a state.

What is proved: one law for each reader and writer of that file, but for `S.onlyInLink`, which has none, and those named
under Limits.
  1, 2  readers whose value the wiping does not change, `(wipeS s).f = s.f`: the fields book, roots, rowsOwed, failed,
        out, req; atBetween, fork?, tl?, look?, lookHeard?, heard5?, funs?, own?, headX?, stages?, inLink, noneWaits,
        closeOk, reqT, tokv, rowR, rowE, reqOk, coveredAt, replyTok?, covered
  3     readers whose value is wiped with the state: `link?_wipe`, `frame_wipe` (and `live_wipe`, Honest/K10/WipeS.lean)
  4     writers of fields that are not wiped, `wipeS (s.put x) = (wipeS s).put x`: mark, putFork, putTl, putLook,
        hearLook, hear5, owe, withReq
  5     writers and movers of a frame: putLink and putLive (the wiped state is handed the wiped value), enterLay,
        enterAtt, enterHead, openHead, enterFin, enterMem, leaveLink
  6     the forms that can refuse, `(wipeS s).f? x = (s.f? x).map wipeS`: the same refusal at both states, or the value
        wiped
  7     wiping twice is wiping once: `wipeS_idem` and its parts
  8     `wipeD`: the record that the ground functions carry, with its statement wiped

By what. A state is taken apart into its fields and the six kinds of place at which the chain can stand; in the head's
link also by whether the link is open; where a function marks, by whether a mark stands; where it asks whether a part is
laid, by that part. Then both sides are the same term. The forms that can refuse follow from the plain forms and
`unmarked_wipe`.

Limits. The laws hold at all states, whether a run can reach them or not. Nothing is said of S.ctx, back, call, callE,
of the starts, or of firstEnd?, fin, finAsked and S.rows. `enterFin_wipe` rests on the default value of a group's row
having the target zero (`row_default`). No member of the chain is named here. No property of the protocol is claimed:
nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.WipeS
import Johnson.Desc.ProofFile.Honest.K10.BatWipe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement Oracle GroupRow zeroE)
open OnBytes.Model (ChainCheck LinkCtx Fork HTailF2)
open VerifiableInference.Desc.First (S Here FinOwn)

/-! ## 1 The fields -/

/-- The wiped state's statement is the state's, wiped. -/
theorem st_wipe (s : S) : (wipeS s).st = wipeSt s.st := rfl

/-- The walk's own state of the calls in the wiped state is the state's, wiped. -/
theorem check_wipe (s : S) : (wipeS s).check = wipeCheck s.check := rfl

/-- What the wiped state holds at its place is what the state holds there, wiped. -/
theorem here_wipe (s : S) : (wipeS s).here = wipeHere s.here := rfl

/-- The wiping leaves the book of trees as it is. -/
theorem book_wipe (s : S) : (wipeS s).book = s.book := rfl

/-- The wiping leaves the number of roots as it is. -/
theorem roots_wipe (s : S) : (wipeS s).roots = s.roots := rfl

/-- The wiping leaves the debt of rows as it is. -/
theorem rowsOwed_wipe (s : S) : (wipeS s).rowsOwed = s.rowsOwed := rfl

/-- The wiping leaves the mark as it is. -/
theorem failed_wipe (s : S) : (wipeS s).failed = s.failed := rfl

/-- The wiping leaves the walk's result as it is. -/
theorem out_wipe (s : S) : (wipeS s).out = s.out := rfl

/-- The wiping leaves the request's words as they are. -/
theorem req_wipe (s : S) : (wipeS s).req = s.req := rfl

/-- The wiping leaves the heard reply as it is. -/
theorem reply_wipe (s : S) : (wipeS s).out.reply = s.out.reply := rfl

/-! ## 2 Readers whose value the wiping does not change -/

/-- Whether the chain stands between two links is the same at a state and at that state wiped. -/
theorem atBetween_wipe (s : S) : (wipeS s).atBetween = s.atBetween := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- The sub-proof's engine is the same at a state and at that state wiped. -/
theorem fork?_wipe (s : S) : (wipeS s).fork? = s.fork? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The smallness test's record is the same at a state and at that state wiped. -/
theorem tl?_wipe (s : S) : (wipeS s).tl? = s.tl? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- What the lookup on the calls returned is the same at a state and at that state wiped. -/
theorem look?_wipe (s : S) : (wipeS s).look? = s.look? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- What the hearing of the lookup laid is the same at a state and at that state wiped. -/
theorem lookHeard?_wipe (s : S) : (wipeS s).lookHeard? = s.lookHeard? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- What an attention segment's own rounds handed on is the same at a state and at that state wiped. -/
theorem heard5?_wipe (s : S) : (wipeS s).heard5? = s.heard5? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- The tables with their weights are the same at a state and at that state wiped. -/
theorem funs?_wipe (s : S) : (wipeS s).funs? = s.funs? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- What a layers' link's own rounds returned is the same at a state and at that state wiped. -/
theorem own?_wipe (s : S) : (wipeS s).own? = s.own? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- What the head's own rounds heard is the same at a state and at that state wiped. -/
theorem headX?_wipe (s : S) : (wipeS s).headX? = s.headX? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The finish's stages are the same at a state and at that state wiped. -/
theorem stages?_wipe (s : S) : (wipeS s).stages? = s.stages? := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Whether a link is open is the same at a state and at that state wiped. -/
theorem inLink_wipe (s : S) : (wipeS s).inLink = s.inLink := by
  unfold S.inLink
  rw [fork?_wipe]

/-- Whether a count waits is the same at a state and at that state wiped. -/
theorem noneWaits_wipe (s : S) : (wipeS s).noneWaits = s.noneWaits := rfl

/-- Whether a round may be closed is the same at a state and at that state wiped. -/
theorem closeOk_wipe (s : S) : (wipeS s).closeOk = s.closeOk := rfl

/-- The number of the request's tokens is the same at a state and at that state wiped. -/
theorem reqT_wipe (s : S) : (wipeS s).reqT = s.reqT := by
  unfold S.reqT
  rw [req_wipe]

/-- The request's tokens are the same at a state and at that state wiped. -/
theorem tokv_wipe (s : S) : (wipeS s).tokv = s.tokv := by
  unfold S.tokv
  rw [req_wipe, reqT_wipe]

/-- The first covered position is the same at a state and at that state wiped. -/
theorem rowR_wipe (s : S) : (wipeS s).rowR = s.rowR := by
  unfold S.rowR
  rw [req_wipe, reqT_wipe]

/-- The position after the last covered one is the same at a state and at that state wiped. -/
theorem rowE_wipe (s : S) : (wipeS s).rowE = s.rowE := by
  unfold S.rowE
  rw [req_wipe, reqT_wipe]

/-- The tests on the request are the same at a state and at that state wiped. -/
theorem reqOk_wipe (T V : Nat) (s : S) : S.reqOk T V (wipeS s) = S.reqOk T V s := by
  unfold S.reqOk
  rw [req_wipe, tokv_wipe, rowR_wipe, rowE_wipe]

/-- The covered positions at a given reply are the same at a state and at that state wiped. -/
theorem coveredAt_wipe (T V y : Nat) (s : S) : S.coveredAt T V y (wipeS s) = S.coveredAt T V y s := by
  unfold S.coveredAt
  rw [req_wipe]

/-- The heard reply as a token's number is the same at a state and at that state wiped. -/
theorem replyTok?_wipe (s : S) : (wipeS s).replyTok? = s.replyTok? := by
  unfold S.replyTok?
  rw [out_wipe]

/-- The covered positions are the same at a state and at that state wiped. -/
theorem covered_wipe (T V : Nat) (s : S) : S.covered T V (wipeS s) = S.covered T V s := by
  unfold S.covered
  rw [replyTok?_wipe]
  cases s.replyTok? with
  | none => rfl
  | some y => exact coveredAt_wipe T V y s

/-! ## 3 Readers whose value is wiped with the state (`live_wipe` stands in Honest/K10/WipeS.lean) -/

/-- The open link's context at the wiped state is the state's, wiped. -/
theorem link?_wipe (s : S) : (wipeS s).link? = s.link?.map wipeCtx := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Whether a link's context is there is the same at a state and at that state wiped. -/
theorem linkSome_wipe (s : S) : (wipeS s).link?.isSome = s.link?.isSome := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The frame that the calls turn, at the wiped state, is the state's, wiped. -/
theorem frame_wipe (s : S) : (wipeS s).frame = wipeFrame s.frame := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-! ## 4 Writers of fields that are not wiped -/

/-- Marking a state and wiping give the same state in either order. -/
theorem mark_wipe (s : S) (name : String) : wipeS (s.mark name) = (wipeS s).mark name := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _, _⟩ <;> rfl

/-- Laying the engine and wiping give the same state in either order. -/
theorem putFork_wipe (s : S) (F : Fork) : wipeS (s.putFork F) = (wipeS s).putFork F := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Laying the smallness test's record and wiping give the same state in either order. -/
theorem putTl_wipe (s : S) (tl : HTailF2) : wipeS (s.putTl tl) = (wipeS s).putTl tl := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Laying the lookup's value and wiping give the same state in either order. -/
theorem putLook_wipe (s : S) (g : OnBytes.Model.Forest.Heard) : wipeS (s.putLook g) = (wipeS s).putLook g := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | ⟨_, _, _ | _, _, _, _⟩ | ⟨_, _, _, _ | _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Hearing the lookup and wiping give the same state in either order. -/
theorem hearLook_wipe (s : S) (g : OnBytes.Model.Forest.Heard) : wipeS (s.hearLook g) = (wipeS s).hearLook g := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | ⟨_, _, _, _, _, _ | _⟩ | ⟨_, _, _, _, _, _, _, _, _, _ | _, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _ | _⟩ | _ | _, _⟩ <;> rfl

/-- Hearing an attention segment's own rounds and wiping give the same state in either order. -/
theorem hear5_wipe (s : S) (h : VerifiableInference.Desc.First.Att.P.Heard) :
    wipeS (s.hear5 h) = (wipeS s).hear5 h := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | ⟨_, _, _, _, _, _, _, _, _, _, _ | _⟩ |
    _ | _ | _, _⟩ <;> rfl

/-- Laying a debt of rows and wiping give the same state in either order. -/
theorem owe_wipe (s : S) (rows : Nat) : wipeS (s.owe rows) = (wipeS s).owe rows := by
  unfold S.owe
  rw [noneWaits_wipe]
  by_cases h : s.noneWaits = true
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    exact mark_wipe s _

/-- Laying the request's words and wiping give the same state in either order. -/
theorem withReq_wipe (s : S) (req : Array UInt32) : wipeS (s.withReq req) = (wipeS s).withReq req := rfl

/-! ## 5 Writers and movers of a frame -/

/-- Laying a link's context and then wiping gives what laying the wiped context into the wiped state gives. -/
theorem putLink_wipe (s : S) (L : LinkCtx) : wipeS (s.putLink L) = (wipeS s).putLink (wipeCtx L) := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Laying the live state of the calls and then wiping gives what laying the wiped one into the wiped state gives. -/
theorem putLive_wipe (s : S) (c : ChainCheck) : wipeS (s.putLive c) = (wipeS s).putLive (wipeCheck c) := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- Entering a layers' link and then wiping gives what entering it from the wiped state with the wiped context
gives. -/
theorem enterLay_wipe (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    wipeS (s.enterLay L F tl) = (wipeS s).enterLay (wipeCtx L) F tl := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Entering an attention link and then wiping gives what entering it from the wiped state with the wiped context
gives. -/
theorem enterAtt_wipe (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    wipeS (s.enterAtt L F tl) = (wipeS s).enterAtt (wipeCtx L) F tl := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Entering the head's link, which copies the walk's frame twice, and wiping give the same state in either order. -/
theorem enterHead_wipe (s : S) (tl : HTailF2) : wipeS (s.enterHead tl) = (wipeS s).enterHead tl := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Opening the head's link, which copies the walk's state of the calls, and wiping give the same state in either
order. -/
theorem openHead_wipe (s : S) : wipeS s.openHead = (wipeS s).openHead := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- The default value of a group's row already has the target zero. -/
theorem row_default : ({ (default : GroupRow) with target := zeroE } : GroupRow) = default := rfl

/-- Entering the finish, which copies the walk's frame and lays a default row, and wiping give the same state in
either order. -/
theorem enterFin_wipe (s : S) : wipeS s.enterFin = (wipeS s).enterFin := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Entering the members' places and wiping give the same state in either order. -/
theorem enterMem_wipe (s : S) : wipeS s.enterMem = (wipeS s).enterMem := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- Leaving a link, which takes the live state of the calls back, and wiping give the same state in either order. -/
theorem leaveLink_wipe (s : S) : wipeS s.leaveLink = (wipeS s).leaveLink := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-! ## 6 The forms that refuse -/

/-- The test for a mark, at the wiped state: the same refusal as at the state, or the state wiped. -/
theorem unmarked_wipe (s : S) : (wipeS s).unmarked = s.unmarked.map wipeS := by
  rcases s with ⟨_, _, _, _, _ | _, _, _, _, _⟩ <;> rfl

/-- `S.putFork?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem putFork?_wipe (s : S) (F : Fork) :
    (wipeS s).putFork? F = (s.putFork? F).map wipeS := by
  unfold S.putFork?
  rw [fork?_wipe, ← putFork_wipe, unmarked_wipe]
  cases s.fork?.isSome <;> rfl

/-- `S.putLink?` at the wiped state and the wiped context: the same refusal as at the state, or that value wiped. -/
theorem putLink?_wipe (s : S) (L : LinkCtx) :
    (wipeS s).putLink? (wipeCtx L) = (s.putLink? L).map wipeS := by
  unfold S.putLink?
  rw [linkSome_wipe, ← putLink_wipe, unmarked_wipe]
  cases s.link?.isSome <;> rfl

/-- `S.putTl?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem putTl?_wipe (s : S) (tl : HTailF2) :
    (wipeS s).putTl? tl = (s.putTl? tl).map wipeS := by
  unfold S.putTl?
  rw [tl?_wipe, ← putTl_wipe, unmarked_wipe]
  cases s.tl?.isSome <;> rfl

/-- `S.putLook?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem putLook?_wipe (s : S) (g : OnBytes.Model.Forest.Heard) :
    (wipeS s).putLook? g = (s.putLook? g).map wipeS := by
  unfold S.putLook?
  rw [look?_wipe, ← putLook_wipe, unmarked_wipe]
  cases s.look?.isSome <;> rfl

/-- `S.hearLook?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem hearLook?_wipe (s : S) (g : OnBytes.Model.Forest.Heard) :
    (wipeS s).hearLook? g = (s.hearLook? g).map wipeS := by
  unfold S.hearLook?
  rw [← hearLook_wipe, unmarked_wipe]

/-- `S.hear5?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem hear5?_wipe (s : S) (h : VerifiableInference.Desc.First.Att.P.Heard) :
    (wipeS s).hear5? h = (s.hear5? h).map wipeS := by
  unfold S.hear5?
  rw [← hear5_wipe, unmarked_wipe]

/-- `S.putLive?` at the wiped state and the wiped state of the calls: the same refusal as at the state, or that
value wiped. -/
theorem putLive?_wipe (s : S) (c : ChainCheck) :
    (wipeS s).putLive? (wipeCheck c) = (s.putLive? c).map wipeS := by
  unfold S.putLive?
  rw [← putLive_wipe, unmarked_wipe]

/-- `S.enterLay?` at the wiped state and the wiped context: the same refusal as at the state, or that value wiped. -/
theorem enterLay?_wipe (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (wipeS s).enterLay? (wipeCtx L) F tl = (s.enterLay? L F tl).map wipeS := by
  unfold S.enterLay?
  rw [← enterLay_wipe, unmarked_wipe]

/-- `S.enterAtt?` at the wiped state and the wiped context: the same refusal as at the state, or that value wiped. -/
theorem enterAtt?_wipe (s : S) (L : LinkCtx) (F : Fork) (tl : HTailF2) :
    (wipeS s).enterAtt? (wipeCtx L) F tl = (s.enterAtt? L F tl).map wipeS := by
  unfold S.enterAtt?
  rw [← enterAtt_wipe, unmarked_wipe]

/-- `S.enterHead?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem enterHead?_wipe (s : S) (tl : HTailF2) :
    (wipeS s).enterHead? tl = (s.enterHead? tl).map wipeS := by
  unfold S.enterHead?
  rw [← enterHead_wipe, unmarked_wipe]

/-- `S.openHead?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem openHead?_wipe (s : S) :
    (wipeS s).openHead? = (s.openHead?).map wipeS := by
  unfold S.openHead?
  rw [← openHead_wipe, unmarked_wipe]

/-- `S.enterFin?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem enterFin?_wipe (s : S) :
    (wipeS s).enterFin? = (s.enterFin?).map wipeS := by
  unfold S.enterFin?
  rw [← enterFin_wipe, unmarked_wipe]

/-- `S.enterMem?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem enterMem?_wipe (s : S) :
    (wipeS s).enterMem? = (s.enterMem?).map wipeS := by
  unfold S.enterMem?
  rw [← enterMem_wipe, unmarked_wipe]

/-- `S.leaveLink?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem leaveLink?_wipe (s : S) :
    (wipeS s).leaveLink? = (s.leaveLink?).map wipeS := by
  unfold S.leaveLink?
  rw [← leaveLink_wipe, unmarked_wipe]

/-- `S.owe?` at the wiped state: the same refusal as at the state, or that value wiped. -/
theorem owe?_wipe (s : S) (rows : Nat) :
    (wipeS s).owe? rows = (s.owe? rows).map wipeS := by
  unfold S.owe?
  rw [← owe_wipe, unmarked_wipe]

/-- `S.closed` at the wiped state yields nothing where it yields nothing at the state, and else that value wiped. -/
theorem closed_wipe (s : S) (rows : Nat) : (wipeS s).closed rows = (s.closed rows).map wipeS := by
  unfold S.closed
  rw [noneWaits_wipe, ← owe_wipe]
  cases s.noneWaits <;> rfl

/-- `S.pay` at the wiped state yields nothing where it yields nothing at the state, and else that value wiped. -/
theorem pay_wipe (s : S) (rows : Nat) : (wipeS s).pay rows = (s.pay rows).map wipeS := by
  rcases s with ⟨_, _, _, _ | n, _, _, _, _, _⟩
  · rfl
  · show (if (n == rows) = true then some _ else none) =
      Option.map wipeS (if (n == rows) = true then some _ else none)
    cases (n == rows) <;> rfl

/-! ## 7 A second wiping changes nothing -/

/-- Mapping an array twice by a function f with f (f x) = f x is mapping it once. -/
theorem map_idem {α : Type} (f : α → α) (h : ∀ x, f (f x) = f x) (a : Array α) : (a.map f).map f = a.map f := by
  rw [Array.map_map]
  exact congrArg (fun g => a.map g) (funext h)

/-- An oracle message wiped twice is that message wiped once. -/
theorem wipeOr_idem (o : Oracle) : wipeOr (wipeOr o) = wipeOr o := by
  show ({ o with sampleRows := (o.sampleRows.map wipeRow).map wipeRow } : Oracle) =
    { o with sampleRows := o.sampleRows.map wipeRow }
  rw [map_idem wipeRow fun _ => rfl]

/-- A group wiped twice is that group wiped once. -/
theorem wipeGr_idem (G : OnBytes.Group) : wipeGr (wipeGr G) = wipeGr G := by
  show ({ G with rows := (G.rows.map wipeRow).map wipeRow } : OnBytes.Group) = { G with rows := G.rows.map wipeRow }
  rw [map_idem wipeRow fun _ => rfl]

/-- A statement wiped twice is that statement wiped once. -/
theorem wipeSt_idem (S : Statement) : wipeSt (wipeSt S) = wipeSt S := by
  show (⟨S.codes, (S.oracles.map wipeOr).map wipeOr, (S.groups.map wipeGr).map wipeGr⟩ : Statement) =
    ⟨S.codes, S.oracles.map wipeOr, S.groups.map wipeGr⟩
  rw [map_idem wipeOr wipeOr_idem, map_idem wipeGr wipeGr_idem]

/-- A state of the calls wiped twice is that state wiped once. -/
theorem wipeCheck_idem (c : ChainCheck) : wipeCheck (wipeCheck c) = wipeCheck c := rfl

/-- A link's context wiped twice is that context wiped once. -/
theorem wipeCtx_idem (L : LinkCtx) : wipeCtx (wipeCtx L) = wipeCtx L := rfl

/-- What is held at a place, wiped twice, is the same wiped once. -/
theorem wipeHere_idem (h : Here) : wipeHere (wipeHere h) = wipeHere h := by
  cases h <;> rfl

/-- **A state wiped twice is that state wiped once.** -/
theorem wipeS_idem (s : S) : wipeS (wipeS s) = wipeS s := by
  show ({ s with st := wipeSt (wipeSt s.st), check := wipeCheck (wipeCheck s.check),
                 here := wipeHere (wipeHere s.here) } : S) =
    { s with st := wipeSt s.st, check := wipeCheck s.check, here := wipeHere s.here }
  rw [wipeSt_idem, wipeCheck_idem, wipeHere_idem]

/-! ## 8 The ground's carried record -/

/-- The ground's carried record with its statement wiped. -/
def wipeD {L : Type} (d : _root_.Desc.Plain.DState L) : _root_.Desc.Plain.DState L :=
  { d with st := wipeSt d.st }

/-- A carried record wiped twice is that record wiped once. -/
theorem wipeD_idem {L : Type} (d : _root_.Desc.Plain.DState L) : wipeD (wipeD d) = wipeD d := by
  show ({ d with st := wipeSt (wipeSt d.st) } : _root_.Desc.Plain.DState L) = { d with st := wipeSt d.st }
  rw [wipeSt_idem]

/-- In the finish the wiping of the batched row is `wipeG`. -/
theorem finRow_wipe (a : FinOwn) :
    wipeHere (.fin a) = .fin { a with fr := wipeFrame a.fr, row := wipeG a.row } := rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.st_wipe
#print axioms ProofFile.Honest.K10.check_wipe
#print axioms ProofFile.Honest.K10.here_wipe
#print axioms ProofFile.Honest.K10.book_wipe
#print axioms ProofFile.Honest.K10.roots_wipe
#print axioms ProofFile.Honest.K10.rowsOwed_wipe
#print axioms ProofFile.Honest.K10.failed_wipe
#print axioms ProofFile.Honest.K10.out_wipe
#print axioms ProofFile.Honest.K10.req_wipe
#print axioms ProofFile.Honest.K10.reply_wipe
#print axioms ProofFile.Honest.K10.atBetween_wipe
#print axioms ProofFile.Honest.K10.fork?_wipe
#print axioms ProofFile.Honest.K10.tl?_wipe
#print axioms ProofFile.Honest.K10.look?_wipe
#print axioms ProofFile.Honest.K10.lookHeard?_wipe
#print axioms ProofFile.Honest.K10.heard5?_wipe
#print axioms ProofFile.Honest.K10.funs?_wipe
#print axioms ProofFile.Honest.K10.own?_wipe
#print axioms ProofFile.Honest.K10.headX?_wipe
#print axioms ProofFile.Honest.K10.stages?_wipe
#print axioms ProofFile.Honest.K10.inLink_wipe
#print axioms ProofFile.Honest.K10.noneWaits_wipe
#print axioms ProofFile.Honest.K10.closeOk_wipe
#print axioms ProofFile.Honest.K10.reqT_wipe
#print axioms ProofFile.Honest.K10.tokv_wipe
#print axioms ProofFile.Honest.K10.rowR_wipe
#print axioms ProofFile.Honest.K10.rowE_wipe
#print axioms ProofFile.Honest.K10.reqOk_wipe
#print axioms ProofFile.Honest.K10.coveredAt_wipe
#print axioms ProofFile.Honest.K10.replyTok?_wipe
#print axioms ProofFile.Honest.K10.covered_wipe
#print axioms ProofFile.Honest.K10.link?_wipe
#print axioms ProofFile.Honest.K10.linkSome_wipe
#print axioms ProofFile.Honest.K10.frame_wipe
#print axioms ProofFile.Honest.K10.mark_wipe
#print axioms ProofFile.Honest.K10.putFork_wipe
#print axioms ProofFile.Honest.K10.putTl_wipe
#print axioms ProofFile.Honest.K10.putLook_wipe
#print axioms ProofFile.Honest.K10.hearLook_wipe
#print axioms ProofFile.Honest.K10.hear5_wipe
#print axioms ProofFile.Honest.K10.owe_wipe
#print axioms ProofFile.Honest.K10.withReq_wipe
#print axioms ProofFile.Honest.K10.putLink_wipe
#print axioms ProofFile.Honest.K10.putLive_wipe
#print axioms ProofFile.Honest.K10.enterLay_wipe
#print axioms ProofFile.Honest.K10.enterAtt_wipe
#print axioms ProofFile.Honest.K10.enterHead_wipe
#print axioms ProofFile.Honest.K10.openHead_wipe
#print axioms ProofFile.Honest.K10.row_default
#print axioms ProofFile.Honest.K10.enterFin_wipe
#print axioms ProofFile.Honest.K10.enterMem_wipe
#print axioms ProofFile.Honest.K10.leaveLink_wipe
#print axioms ProofFile.Honest.K10.unmarked_wipe
#print axioms ProofFile.Honest.K10.putFork?_wipe
#print axioms ProofFile.Honest.K10.putLink?_wipe
#print axioms ProofFile.Honest.K10.putTl?_wipe
#print axioms ProofFile.Honest.K10.putLook?_wipe
#print axioms ProofFile.Honest.K10.hearLook?_wipe
#print axioms ProofFile.Honest.K10.hear5?_wipe
#print axioms ProofFile.Honest.K10.putLive?_wipe
#print axioms ProofFile.Honest.K10.enterLay?_wipe
#print axioms ProofFile.Honest.K10.enterAtt?_wipe
#print axioms ProofFile.Honest.K10.enterHead?_wipe
#print axioms ProofFile.Honest.K10.openHead?_wipe
#print axioms ProofFile.Honest.K10.enterFin?_wipe
#print axioms ProofFile.Honest.K10.enterMem?_wipe
#print axioms ProofFile.Honest.K10.leaveLink?_wipe
#print axioms ProofFile.Honest.K10.owe?_wipe
#print axioms ProofFile.Honest.K10.closed_wipe
#print axioms ProofFile.Honest.K10.pay_wipe
#print axioms ProofFile.Honest.K10.map_idem
#print axioms ProofFile.Honest.K10.wipeOr_idem
#print axioms ProofFile.Honest.K10.wipeGr_idem
#print axioms ProofFile.Honest.K10.wipeSt_idem
#print axioms ProofFile.Honest.K10.wipeCheck_idem
#print axioms ProofFile.Honest.K10.wipeCtx_idem
#print axioms ProofFile.Honest.K10.wipeHere_idem
#print axioms ProofFile.Honest.K10.wipeS_idem
#print axioms ProofFile.Honest.K10.wipeD
#print axioms ProofFile.Honest.K10.wipeD_idem
#print axioms ProofFile.Honest.K10.finRow_wipe
