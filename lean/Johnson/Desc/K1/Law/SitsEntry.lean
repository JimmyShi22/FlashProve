-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SitsEntry.lean: THE ROW K01_sits AT THE KIND K1's ONE PLACE OF THE ENTRY FILE's
DESCRIPTION (⟨1, none, 2, .K1⟩ "send o_0, o_1"; `Desc.K15.linkDescriptionAt`, Johnson/Desc/Link/LinkDesc.lean):
the seat, the wrapper's yes, the numbers: WITH NO PREMISE, at the written parameters frP.

Statements and proofs.
Main names:
  blocksOrV_send: at any parameters P at which the link's rounds can be said: entry 1 of `blocksOrV
  P ++ tl` is `sendK1 P`. sendK1_place: it bears the kind K1's place.
  **sendK1_yes**: THE WRAPPER: a yes of `sendK1 P` from d to d' gives a yes of the kind's own block
  `K1.sendOwn (Desc.K15.parK1 P)` at the same rounds and columns, from the state that holds d's
  statement, book, roots and columns and owes no count.
  entry_test: one evaluation in Lean's kernel: frP's codes are the written list codesFull1; what the
  link announces at frP is the first written sending of the entry file's one chain; every written
  sending of that chain stands under these codes.
  placeOk_entry: `PlaceOk 1 0 0 (Desc.K15.parK1 frP)`.
  **k01_sits_entry**: seat, place and numbers at `linkDescriptionAt frP plan ok`, whatever plan and ok: so at
  the description whose run the entry file's seat's decision is in the goals' scope, by
  `FlashProve.K15_sits_keys` (Johnson/Goal/Conditions/EntrySits.lean), which this file does
  not import.
By decide +kernel, that is, evaluated by Lean's kernel at the written numbers, and to be proved
again when they change: entry_test.
Not claimed here. The four code switches of the link's proximity test: rounds inside one block of
another kind's. That frP is what the planner makes at any files (EntrySits.lean's laws say what the
seat runs). No soundness, no completeness and no hiding is claimed. It holds no coding theory.

-/
import Johnson.Desc.K1.Law.SitsShared
import Johnson.Desc.Link.LinkDoorsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params Johnson.G Desc.Plain
open VerifiableInference.Desc (Block)
open _root_.Desc.K15 (P15 frP sendK1 blocksOrV linkDescriptionAt)

/-- The link's sending among the five blocks in front of the test. -/
theorem blocksOrV_send (P : P15) (hE : (_root_.Desc.K15.entries P).isSome = true)
    (tl : List (Block _root_.Desc.K15.St Unit)) : (blocksOrV P ++ tl)[1]? = some (sendK1 P) := by
  have hb : ∃ b0 b2 b3 b4, _root_.Desc.K15.linkBlocksBeforeTest P = some [b0, sendK1 P, b2, b3, b4] := by
    unfold _root_.Desc.K15.linkBlocksBeforeTest
    cases he : _root_.Desc.K15.entries P with
    | none =>
      rw [he] at hE
      cases hE
    | some es => exact ⟨_, _, _, _, rfl⟩
  obtain ⟨b0, b2, b3, b4, hb⟩ := hb
  unfold blocksOrV
  rw [hb]
  rfl

theorem sendK1_place (P : P15) : (sendK1 P).place = ⟨1, none, 2, .K1⟩ := rfl

/-- **THE WRAPPER's YES.** -/
theorem sendK1_yes (P : P15) {d d' : _root_.Desc.K15.St} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (sendK1 P).decide d rs gs = .ok d') :
    ∃ t : Owing (DState (Array Nat)),
      (sendOwn (Cl := Unit) (_root_.Desc.K15.parK1 P)).decide
        { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                  opened := d.opened, loc := #[] } } rs gs = .ok t := by
  have h' := (VerifiableInference.Desc.K12.Seat.inside_ok _ _ _ d d' rs gs).1
    (show (Block.inside
      (fun d : _root_.Desc.K15.St =>
        .ok { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                      opened := d.opened, loc := #[] } })
      (sendOwn (Cl := Unit) (_root_.Desc.K15.parK1 P))
      (fun d t => named "the sending's numbers are not those that the kind notes"
        (_root_.Desc.K15.behind P.par
          { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                   opened := t.held.opened } t.held.loc))).decide d rs gs = .ok d' from h)
  obtain ⟨t0, t, e0, e1, -⟩ := h'
  cases e0
  exact ⟨t, e1⟩

/-- What K15 notes behind the sending leaves the statement. -/
theorem behind15_st {p : _root_.Desc.K15.Par15} {d d' : _root_.Desc.K15.St} {ids : Array Nat}
    (h : _root_.Desc.K15.behind p d ids = some d') : d'.st = d.st := by
  unfold _root_.Desc.K15.behind at h
  split at h
  all_goals
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, -, _, -, _, -, rfl⟩ := h
    rfl

/-- **The law's own premise at the entry file's sending**: after the shared chain's law
sendAt_isSend. -/
theorem sendK1_isSend (P : P15) :
    IsSend (_root_.Desc.K15.parK1 P) (fun s : _root_.Desc.K15.St => s.st) (sendK1 P) := by
  intro d d' r₁ r₂ gs h
  have h' := (VerifiableInference.Desc.K12.Seat.inside_ok _ _ _ d d' [r₁, r₂] gs).1
    (show (Block.inside
      (fun d : _root_.Desc.K15.St =>
        .ok { owed := none, held := { st := d.st, book := d.book, roots := d.roots,
                                      opened := d.opened, loc := #[] } })
      (sendOwn (Cl := Unit) (_root_.Desc.K15.parK1 P))
      (fun d t => named "the sending's numbers are not those that the kind notes"
        (_root_.Desc.K15.behind P.par
          { d with st := t.held.st, book := t.held.book, roots := t.held.roots,
                   opened := t.held.opened } t.held.loc))).decide d [r₁, r₂] gs = .ok d' from h)
  obtain ⟨t0, t, e0, e1, e2⟩ := h'
  cases e0
  simp only [sendOwn] at e1
  obtain ⟨⟨ids, x2⟩, hx, rfl⟩ := _root_.Desc.K14.Law.emap_ok e1
  have e : d'.st = x2.st := behind15_st (_root_.Desc.K14.Law.named_some e2)
  refine ⟨_, _, x2, none, ids, hx, ?_, ?_⟩
  · show SameMsgs x2.st d'.st
    rw [e]
    exact ⟨rfl, fun _ => rfl⟩
  · show d'.st.oracles.size = x2.st.oracles.size
    rw [e]

set_option maxRecDepth 1000000 in
/-- **The written parameters against the written sendings.** By evaluation in Lean's kernel. -/
theorem entry_test : (decide (frP.codes = codesFull1) &&
    decide ((sentOf 1 0)[0]? = some (_root_.Desc.K15.sent frP).toList) &&
    (litAt sendsFullLit packFullLit 1 0).all fun y => decide (y.2.cs = codesFull1)) = true := by
  decide +kernel

theorem parK1_entry_sent (P : P15) :
    (_root_.Desc.K15.parK1 P).sent = _root_.Desc.K15.sent P := by
  simp [_root_.Desc.K15.parK1, Par.sent]

/-- **THE NUMBERS.** -/
theorem placeOk_entry : PlaceOk 1 0 0 (_root_.Desc.K15.parK1 frP) := by
  have ht := entry_test
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
  obtain ⟨⟨t1, t2⟩, t3⟩ := ht
  unfold sentOf at t2
  rw [List.getElem?_map] at t2
  cases hy : (litAt sendsFullLit packFullLit 1 0)[0]? with
  | none =>
    rw [hy] at t2
    cases t2
  | some y =>
    rw [hy] at t2
    have hs : y.2.sent = (_root_.Desc.K15.sent frP).toList := Option.some.inj t2
    have hm := List.mem_of_getElem? hy
    have h1 : (_root_.Desc.K15.parK1 frP).codes = codesFull1 := t1
    have hat : y.2.At (_root_.Desc.K15.parK1 frP) :=
      ⟨h1.trans (t3 y hm).symm, by rw [hs, parK1_entry_sent]⟩
    exact ⟨y, hy, hat, (((k01_full y.2 (litAt_mem hm)).2).1 _ hat).1⟩

/-- **SEAT, PLACE AND NUMBERS AT THE ENTRY FILE's ONE PLACE OF THE KIND.** -/
theorem k01_sits_entry (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt frP plan ok).chain.back[1]? = some (sendK1 frP) ∧
      (sendK1 frP).place = ⟨1, none, 2, .K1⟩ ∧
      IsSend (_root_.Desc.K15.parK1 frP) (fun s : _root_.Desc.K15.St => s.st) (sendK1 frP) ∧
      PlaceOk 1 0 0 (_root_.Desc.K15.parK1 frP) :=
  ⟨blocksOrV_send frP _root_.Desc.K15.entries_full _, rfl, sendK1_isSend frP, placeOk_entry⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.blocksOrV_send
#print axioms VerifiableInference.Desc.K1.sendK1_place
#print axioms VerifiableInference.Desc.K1.sendK1_yes
#print axioms VerifiableInference.Desc.K1.behind15_st
#print axioms VerifiableInference.Desc.K1.sendK1_isSend
#print axioms VerifiableInference.Desc.K1.entry_test
#print axioms VerifiableInference.Desc.K1.parK1_entry_sent
#print axioms VerifiableInference.Desc.K1.placeOk_entry
#print axioms VerifiableInference.Desc.K1.k01_sits_entry
