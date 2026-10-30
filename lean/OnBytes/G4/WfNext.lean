-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfNext.lean: from one lookup of a key's one-time chain to the next: the context that a
call of the lookup verifier leaves is ready for the next call.

What WfCallReady (OnBytes/G4/WfCall.lean) asks of a context falls into three kinds. What a lookup
does not turn: the test wfFacts and the test on mask entries read the messages' shapes, their
entries that mask answers to samples, and the group's members and mark; a lookup turns the two
ledgers and the group's rows alone (`wfFacts_ctx`, `slotB_ctx`, `left_ctx`). What the context that
is left has by its making: the three marks, no open round, the two ledgers, the group, its entries
and rounds. And what the call's own law hands on: the rounds that are left fit the entries that are
left, and what the ledgers have left. `WfCallReady.next`: let a context be ready for lookup i, with
the entries behind the lookup's own being those of lookup j (under a number of bits of work of its
own) and then es''. If the test wfFacts holds for j at the same context, the public inputs of j are
Ready, and the ledgers have room for both lookups, then the context that the call for i leaves is
ready for j, with the same arbitrary tail behind the lookups.

`takesOf_add_snd`, `takesOf_entries`: a ledger's takes are total and additive: behind k takes the
next n are the entries number k, .., k + n - 1 of one enumeration (`entryOf`), whatever the ledger
counts as left.

Main theorems: wfFacts_ctx, slotB_ctx, left_ctx, WfCallReady.next, takesOf_add_snd, takesOf_entries.
Not claimed. What stands between two calls in Wf.lookupsVerify (Wf.pendingOf) is not treated: it
must leave the context as it is.


-/
import OnBytes.G4.WfCall

set_option autoImplicit false

namespace OnBytes.G4

open Blk OnBytes.Params

section
variable (c : Ctx) (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (i j group indexMasksId : Nat)
variable (es : List Fmt.Entry) (cur : Option Fmt.RoundView) (rs : List Fmt.RoundView) (last : Option Fmt.Entry)
variable (σ : Ledger × Ledger) (rows : Array Row)

/-- The group of the context that a lookup leaves is the group with other rows. -/
theorem groupOf_ctx (G : Group) (hG : c.st.groups[group]? = some G) :
    (wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j group
      indexMasksId).groupOf = { G with rows := rows } := by
  show ((((wfSeat c x m codes i group indexMasksId).st σ rows).groups[group]?).getD default) = _
  simp [Seat.st, wfSeat, Array.getElem?_modify, hG]

theorem groupOf_base (G : Group) (hG : c.st.groups[group]? = some G) :
    (wfSeat c x m codes j group indexMasksId).groupOf = G := by
  show ((c.st.groups[group]?).getD default) = _
  simp [hG]

theorem padsOf_ctx (q : Nat) :
    (wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j group
      indexMasksId).padsOf q = (wfSeat c x m codes j group indexMasksId).padsOf q :=
  Seat.pad_st (wfSeat c x m codes i group indexMasksId) σ rows q

/-- The test on a mask entry does not turn. -/
theorem slotB_ctx (G : Group) (hG : c.st.groups[group]? = some G) (s : Slot) :
    (wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j group
      indexMasksId).slotB s = (wfSeat c x m codes j group indexMasksId).slotB s := by
  unfold Seat.slotB
  rw [groupOf_ctx c x m codes i j group indexMasksId es cur rs last σ rows G hG,
    groupOf_base c x m codes j group indexMasksId G hG]
  simp only [padsOf_ctx]
  have e1 : placeOk
      (wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m
      codes j group indexMasksId).base.st { G with rows := rows } s.oracle .mask
      ((wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j
          group
        indexMasksId).base.st.tableBits s.oracle .mask) s.index =
      placeOk (wfSeat c x m codes j group indexMasksId).base.st G s.oracle .mask
        ((wfSeat c x m codes j group indexMasksId).base.st.tableBits s.oracle .mask) s.index := by
    show placeOk ((wfSeat c x m codes i group indexMasksId).st σ rows) { G with rows := rows }
        s.oracle
      .mask (((wfSeat c x m codes i group indexMasksId).st σ rows).tableBits s.oracle .mask) s.index
          = _
    rw [Seat.placeOk_st, Seat.tableBits_st]
    rfl
  rw [e1]

/-- What the first ledger counts as left does not turn. -/
theorem left_ctx (G : Group) (hG : c.st.groups[group]? = some G) (τ : Ledger × Ledger) :
    (wfSeat ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j group
      indexMasksId).caller.left τ = (wfSeat c x m codes j group indexMasksId).caller.left τ := by
  show (if Seat.ledB _ x.messageId τ.1 then τ.1.left else 0) =
    (if Seat.ledB _ x.messageId τ.1 then τ.1.left else 0)
  unfold Seat.ledB
  simp only [slotB_ctx c x m codes i j group indexMasksId es cur rs last σ rows G hG]

/-- The test on the statement does not turn. -/
theorem wfFacts_ctx (G : Group) (hG : c.st.groups[group]? = some G) :
    wfFacts ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows) x m codes j group
      indexMasksId = wfFacts c x m codes j group indexMasksId := by
  unfold wfFacts
  simp only [groupOf_ctx c x m codes i j group indexMasksId es cur rs last σ rows G hG,
    groupOf_base c x m codes j group indexMasksId G hG, padsOf_ctx]
  have o1 : ∀ o : Nat,
      ((((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows).st.oracles[o]?).any
      Oracle.sampled) = ((c.st.oracles[o]?).any Oracle.sampled) := by
    intro o
    show ((((wfSeat c x m codes i group indexMasksId).st σ rows).oracles[o]?).any Oracle.sampled) =
        _
    rw [Seat.oracleAt]
    show (((c.st.oracles[o]?).map _).any Oracle.sampled) = _
    cases c.st.oracles[o]? <;> simp [Seat.fix_sampled]
  have g1 : ((((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ
      rows).st.groups[group]?).isSome) =
      ((c.st.groups[group]?).isSome) := by
    show ((((wfSeat c x m codes i group indexMasksId).st σ rows).groups[group]?).isSome) = _
    simp [Seat.st, wfSeat, Array.getElem?_modify, hG]
  have p1 : ∀ n : Nat, placeOk
      ((wfSeat c x m codes i group indexMasksId).ctx es cur rs last σ rows).st
      { G with rows := rows } x.messageId .main n 0 = placeOk c.st G x.messageId .main n 0 := by
    intro n
    exact Seat.placeOk_st (wfSeat c x m codes i group indexMasksId) σ rows G rows _ _ _ _
  simp only [o1, g1, p1]

end

/-- FROM ONE LOOKUP TO THE NEXT. The context that the call for lookup i leaves is ready for lookup
j, with the same tail behind it. -/
theorem WfCallReady.next {c : Ctx} {x : WfPublic} {m : Wf.Matrix} {codes : Codes}
    {i group indexMasksId work : Nat} (j work' : Nat) {rs : List FlatRound}
    {es'' tailEntries : List Fmt.Entry} {tailRounds : List Fmt.RoundView} {l1 l2 : Ledger} {G : Group}
    (h : WfCallReady c x m codes i group indexMasksId work rs
      (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es'') tailEntries
          tailRounds l1 l2 G)
    (hfacts : wfFacts c x m codes j group indexMasksId = true)
    (hready : Ready (Wf.lookupOf x.messageId m (x.lookups.getD j default)))
    (hroom : ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) +
        ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD j default)) ≤
      (wfSeat c x m codes i group indexMasksId).caller.left (l1, l2))
    (hkey : treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts +
        treesKey (Wf.lookupOf x.messageId m (x.lookups.getD j default)).parts ≤
      (wfSeat c x m codes i group indexMasksId).caller.keyLeft (l1, l2)) :
    ∃ last,
      (Lkp.verify (Wf.lookupOf x.messageId m (x.lookups.getD i default)) (Wf.planesAt x codes i)
          x.messageId group (some indexMasksId)) c =
        .ok ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.out,
          (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
              G).course.last.ctx
            (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es'') last)
                ∧
      WfCallReady
        ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.last.ctx
          (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es'') last)
        x m codes j group indexMasksId work'
        (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.last.rounds es''
        tailEntries tailRounds
        (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.last.led.1
        (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.last.led.2
        { G with rows :=
            (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2
            G).course.last.rows } := by
  have g := wfSeat_good c x m codes i group indexMasksId h.facts
  have L := (Seat.laws _ g).withTail tailEntries tailRounds
  obtain ⟨last, hq, hf, hl, hk, _, hrun⟩ := L.verify_val work h.ready _
    (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G) c.ch.last h.noRows
        h.fits h.room h.keyRoom
  obtain ⟨s', hs⟩ : ∃ s, s =
      (wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).course.last :=
      ⟨_, rfl⟩
  have hf' : FitsAll s'.rounds
      (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es'') := by
    rw [hs]
    exact hf
  have hl' : (wfSeat c x m codes i group indexMasksId).caller.left s'.led =
      (wfSeat c x m codes i group indexMasksId).caller.left (l1, l2) -
        ownTotal (Wf.lookupOf x.messageId m (x.lookups.getD i default)) := by
    rw [hs]
    exact hl
  have hk' : (wfSeat c x m codes i group indexMasksId).caller.keyLeft s'.led =
      (wfSeat c x m codes i group indexMasksId).caller.keyLeft (l1, l2) -
        treesKey (Wf.lookupOf x.messageId m (x.lookups.getD i default)).parts := by
    rw [hs]
    exact hk
  rw [← hs]
  obtain ⟨y1, hy1, _⟩ := g.sampled x.messageId (Or.inl rfl)
  obtain ⟨y2, hy2, _⟩ := g.sampled indexMasksId (Or.inr (Or.inl rfl))
  have hne : x.messageId ≠ indexMasksId := g.apart
  refine ⟨last, ?_, ?_⟩
  · have hrun' : (Lkp.verify (Wf.lookupOf x.messageId m (x.lookups.getD i default))
        (Wf.planesAt x codes i) x.messageId group (some indexMasksId))
        ((wfStand c x m codes i group indexMasksId tailEntries tailRounds rs l1 l2 G).ctx
          (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD i default)) work
            (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es''))
          c.ch.last) = _ := hrun
    rw [h.ctx_eq] at hrun'
    rw [hs]
    exact hrun'
  · exact
      { facts := by
          show wfFacts ((wfSeat c x m codes i group indexMasksId).ctx _ none _ last s'.led s'.rows)
              x m
            codes j group indexMasksId = true
          rw [wfFacts_ctx c x m codes i j group indexMasksId _ _ _ _ _ _ G h.theGroup]
          exact hfacts
        view := rfl
        noNotes := rfl
        notAsked := rfl
        closed := rfl
        noRows := hq
        first := by
          show ((((wfSeat c x m codes i group indexMasksId).st s'.led
              s'.rows).oracles[x.messageId]?).bind
            Oracle.ledger) = _
          rw [Seat.oracleAt]
          show (((c.st.oracles[x.messageId]?).map _).bind Oracle.ledger) = _
          rw [show c.st.oracles[x.messageId]? = some y1 from hy1]
          simp [Seat.fix, wfSeat, Ne.symm hne]
        second := by
          show ((((wfSeat c x m codes i group indexMasksId).st s'.led
              s'.rows).oracles[indexMasksId]?).bind
            Oracle.ledger) = _
          rw [Seat.oracleAt]
          show (((c.st.oracles[indexMasksId]?).map _).bind Oracle.ledger) = _
          rw [show c.st.oracles[indexMasksId]? = some y2 from hy2]
          simp [Seat.fix, wfSeat]
        theGroup := by
          show ((wfSeat c x m codes i group indexMasksId).st s'.led s'.rows).groups[group]? = _
          simp [Seat.st, wfSeat, Array.getElem?_modify, h.theGroup]
        ready := hready
        room := by
          have e := left_ctx c x m codes i j group indexMasksId
            ((lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work' es'') ++
                tailEntries) none
            (rvs s'.rounds ++ tailRounds) last s'.led s'.rows G h.theGroup (s'.led.1, s'.led.2)
          have e2 : (wfSeat c x m codes j group indexMasksId).caller.left (s'.led.1, s'.led.2) =
              (wfSeat c x m codes i group indexMasksId).caller.left s'.led := rfl
          refine Nat.le_trans ?_ (Nat.le_of_eq (e.trans e2).symm)
          rw [hl']
          omega
        keyRoom := by
          have e2 : (wfSeat
              (s'.ctx (lookupEntries (Wf.lookupOf x.messageId m (x.lookups.getD j default)) work'
              es'') last) x m
              codes j group indexMasksId).caller.keyLeft (s'.led.1, s'.led.2) =
              (wfSeat c x m codes i group indexMasksId).caller.keyLeft s'.led := rfl
          refine Nat.le_trans ?_ (Nat.le_of_eq e2.symm)
          rw [hk']
          omega
        entries := rfl
        rounds := rfl
        fits := hf' }

/-! ## The takes of a ledger are total and additive -/

/-- Takes in two goes leave the ledger that takes in one leave. No premise: a ledger names its next
entries whether or not it counts them as left. -/
theorem takesOf_add_snd : ∀ (a b : Nat) (l : Ledger),
    (takesOf l (a + b)).2 = (takesOf (takesOf l a).2 b).2
  | 0, b, l => by simp [takesOf]
  | a + 1, b, l => by
    rw [show a + 1 + b = (a + b) + 1 from by omega]
    simp [takesOf, takesOf_add_snd a b]

/-- Entry number k that a ledger gives, counted from 0. -/
def entryOf (l : Ledger) (k : Nat) : Nat := (stepLedger (takesOf l k).2).1

/-- The n takes behind the first k are the entries number k, .., k + n - 1 of the one enumeration.
-/
theorem takesOf_entries : ∀ (n k : Nat) (l : Ledger),
    (takesOf (takesOf l k).2 n).1 = (List.range' k n).map (entryOf l)
  | 0, _, _ => rfl
  | n + 1, k, l => by
    have e : (takesOf l (k + 1)).2 = (stepLedger (takesOf l k).2).2 := by
      rw [takesOf_add_snd]
      rfl
    simp only [takesOf, List.range'_succ, List.map_cons]
    rw [← e, takesOf_entries n (k + 1) l]
    rfl

end OnBytes.G4

#print axioms OnBytes.G4.WfCallReady.next
#print axioms OnBytes.G4.takesOf_entries
