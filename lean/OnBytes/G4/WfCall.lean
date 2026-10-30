-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfCall.lean: the call of the lookup verifier that a key's one-time chain makes
(Wf.lookupsVerify, OnBytes/Iop/Wf.lean), as a function of the rounds, at every context of the
program that is ready for it.

`WfCallReady c x m codes i group indexMasksId work rs es' tailEntries tailRounds` says of a context
c what the call needs. It is one closed statement, made of
 - the test wfFacts (OnBytes/G4/WfSeat.lean) on c's statement and on public numbers;
 - three marks of c: it is no dry run, keeps no intermediate values, and no block has asked for the
   last round's number of rows; no round is open; the entry of the round closed last counts no
   batched rows;
 - the two messages have ledgers; the first is open, all entries that it can still give may be read
   by a row of the group, and it has at least ownTotal entries left; the second is open and has at
   least two for each part;
 - the public inputs are Ready (OnBytes/G4/AnyRun.lean);
 - c's entries are the lookup's entries, then es', then tailEntries; c's rounds are the plain rounds
   rs and then tailRounds; rs fit the lookup's entries and es'. es' is meant for the entries of the
   lookups that follow. tailEntries and tailRounds are ARBITRARY: what stands behind the lookups in
   the chain (rounds that draw positions, answers to samples, a seal) is no plain round, and nothing
   is asked of it. `wf_verify_eq`: at such a context the call gives what the course of the stand
   `wfStand` says, and leaves the
context of the course's last stand, with the same tail behind it.

Main definitions: WfCallReady, wfCaller, wfStand.
Main theorems: WfCallReady.ctx_eq, wf_verify_eq.
Not claimed. That the context in which a key's one-time chain calls the lookups is ready: that is a
hypothesis wherever this file is used for a key. Two of its fields, `rounds` and `fits`, lean on
what the strict reader of the files guarantees of a view, not on anything that the program's blocks
test: that each of the lookups' rounds holds elements alone and draws elements alone, no position,
no matrix entry and no digest; that the drawn words are below p; that a draw is not 0 where the
entry says so. (The blocks refuse another item and compare the numbers of positions and matrix
entries; nothing in them looks at the digest, the words' size or a draw's being 0.) That the premise
can be met is shown at the small object of OnBytes/G4/WfCallToy.lean [not in this library; so here
read: not shown in this library].

-/
import OnBytes.G4.WfSeat
import OnBytes.G4.AnyTail

set_option autoImplicit false

namespace OnBytes.G4

open Blk OnBytes.Params

/-- What the call needs of a context. l1, l2: the two ledgers; G: the group. -/
structure WfCallReady (c : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes)
    (i group indexMasksId work : Nat) (rs : List FlatRound) (es' tailEntries : List Fmt.Entry)
    (tailRounds : List Fmt.RoundView) (l1 l2 : Ledger) (G : Group) : Prop where
  facts : wfFacts c x m codes i group indexMasksId = true
  view : c.ch.dry = false
  noNotes : c.keepNotes = false
  notAsked : c.ch.askedRows = false
  closed : c.ch.cur = none
  noRows : NoRows c.ch.last
  first : (c.st.oracles[x.messageId]?).bind Oracle.ledger = some l1
  second : (c.st.oracles[indexMasksId]?).bind Oracle.ledger = some l2
  theGroup : c.st.groups[group]? = some G
  ready : Ready (Wf.lookupOf x.messageId m (x.lookups.getD i default))
  room : ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) ≤
    (wfSeat c x m codes i group indexMasksId).caller.left (l1, l2)
  keyRoom : treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts ≤
    (wfSeat c x m codes i group indexMasksId).caller.keyLeft (l1, l2)
  entries : c.ch.entries =
    lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD i default)) work es' ++ tailEntries
  rounds : c.ch.left = rvs rs ++ tailRounds
  fits : FitsAll rs (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD i default)) work es')

/-- The caller at the call, with what stands behind the lookups. -/
def wfCaller (c : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (i group indexMasksId : Nat)
    (tailEntries : List Fmt.Entry) (tailRounds : List Fmt.RoundView) : Caller :=
  (wfSeat c x m codes i group indexMasksId).caller.withTail tailEntries tailRounds

/-- The stand at the call: the plain rounds, the two ledgers, the group's rows. -/
def wfStand (c : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (i group indexMasksId : Nat)
    (tailEntries : List Fmt.Entry) (tailRounds : List Fmt.RoundView) (rs : List FlatRound) (l1 l2 : Ledger)
    (G : Group) : (wfCaller c x m codes i group indexMasksId tailEntries tailRounds).Stand :=
  ⟨rs, (l1, l2), G.rows⟩

/-- A context that is ready is the context of its own stand. -/
theorem WfCallReady.ctx_eq {c : Ctx} {x : WfPublic} {m : Wf.Matrix} {codes : Codes}
    {i group indexMasksId work : Nat} {rs : List FlatRound} {es' tailEntries : List Fmt.Entry}
    {tailRounds : List Fmt.RoundView} {l1 l2 : Ledger} {G : Group}
    (h : WfCallReady c x m codes i group indexMasksId work rs es' tailEntries tailRounds l1 l2 G) :
    (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).ctx
      (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD i default)) work es') c.ch.last =
          c := by
  obtain ⟨y1, hy1, hl1⟩ : ∃ y, c.st.oracles[x.messageId]? = some y ∧ y.ledger = some l1 := by
    have := h.first
    cases hy : c.st.oracles[x.messageId]? with
    | none => simp [hy] at this
    | some y => exact ⟨y, rfl, by simpa [hy] using this⟩
  obtain ⟨y2, hy2, hl2⟩ : ∃ y, c.st.oracles[indexMasksId]? = some y ∧ y.ledger = some l2 := by
    have := h.second
    cases hy : c.st.oracles[indexMasksId]? with
    | none => simp [hy] at this
    | some y => exact ⟨y, rfl, by simpa [hy] using this⟩
  have e : (wfSeat c x m codes i group indexMasksId).ctx c.ch.entries c.ch.cur c.ch.left c.ch.last
      (l1, l2) G.rows = c :=
    Seat.ctx_self (wfSeat c x m codes i group indexMasksId) y1 y2 l1 l2 G hy1 hl1 hy2 hl2
      h.theGroup h.view h.noNotes h.notAsked
  rw [h.entries, h.closed, h.rounds] at e
  exact e

/-- THE CALL OF A KEY's ONE-TIME CHAIN AS A FUNCTION. At a context that is ready, the call gives
what the course says. -/
theorem wf_verify_eq (c : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes)
    (i group indexMasksId work : Nat) (rs : List FlatRound) (es' tailEntries : List Fmt.Entry)
    (tailRounds : List Fmt.RoundView) (l1 l2 : Ledger) (G : Group)
    (h : WfCallReady c x m codes i group indexMasksId work rs es' tailEntries tailRounds l1 l2 G) :
    ∃ last, NoRows last ∧
      FitsAll (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
          G).course.last.rounds
        es' ∧
      PointsAt (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts
        (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).course.keys.1 ∧
      (Lkp.verify (Wf.lookupOf x.messageId m (x.lookups.getD i default)) (Wf.planesAt x codes i)
          x.messageId group (some indexMasksId)) c =
        .ok ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.out,
          (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
              G).course.last.ctx es'
            last) := by
  have L := (wfSeat_laws c x m codes i group indexMasksId h.facts).withTail tailEntries tailRounds
  obtain ⟨last, hq, hf, _, _, hp, hrun⟩ := L.verify_val work h.ready es'
    (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G) c.ch.last h.noRows
        h.fits
    h.room h.keyRoom
  refine ⟨last, hq, hf, hp, ?_⟩
  have hrun' : (Lkp.verify (Wf.lookupOf x.messageId m (x.lookups.getD i default))
      (Wf.planesAt x codes i) x.messageId group (some indexMasksId))
      ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).ctx
        (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD i default)) work es') c.ch.last) =
      .ok ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).course.out,
        (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).course.last.ctx
            es'
          last) := hrun
  rw [h.ctx_eq] at hrun'
  exact hrun'

end OnBytes.G4

#print axioms OnBytes.G4.wf_verify_eq
