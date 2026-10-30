-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/FrontFacts.lean: three of the facts that the merge's ties ask of the
verifier's state in front of the merge of the claims on the committed table (the fields left, made
and size of `MergeFront`, EntryFront.lean), FROM FOUR TESTS WITH CODE ON THAT STATE, one equation on
its codes, and three closed premises. Theorems with their proofs, and small values.

Why. The three fields speak of the index masks' message: its ledger is not closed and has an entry
left; that ledger is the ledger of some number of takes since it was made; ni is the size of the
message's mask table. Each follows from tests that others' files list: three as owed at the states
that the verifier reaches (the fields room, pileWithin and msgShapes of `FoldFacts`,
Johnson/Desc/First/FoldFacts.lean, with its field codes), one as a public test inside the table's
condition (`indexIsC`): so none of the three needs an induction of its own along the run.

Which premise gives what.
  left: `roomIsB free0 fvs m s` (Johnson/Top/H0/Walk/FrameEntriesDefs.lean): the ledger is not
    closed and has just free0 less the bearing segments in front of m left; with the closed premise
    that this number is not 0.
  made: `pileWithinC s` (Johnson/Desc/K13/PubK13.lean): its first half says that every ledger in the
    statement fits; `ledgersC` (Johnson/Desc/K13/Law/LedgersC.lean) reads that as `LedgersFit`. That
    the index masks' message has a ledger comes from the premise of left.
  size: `indexIsC ix s` (PubK13.lean): which number the message has; `atFirstShapes M s`
    (Johnson/Desc/K12/Door/MsgShapes.lean): the messages' shapes are the first of the list M; the
    statement's codes are cs; with the closed premises that M has the shape sh at ix, and that ni is
    the size of a mask table of that shape under these codes. That the shape has a mask row is not
    asked: the fact made says it.

Main names:
  `ledger_of_left`: where `leftIsB n s` accepts, the index masks' message is there and has a ledger.
  `left_of_room`, `made_of_pile`, `size_of_shapes`: the three, one by one.
  `front_facts`: THE THREE AT ONE STATE.
  `FactsToy`: a small state without a mark at which all premises are met, and negative tests: six
    values, each altered in one place, at which one test each rejects.

Limits. That the four tests accept and the equation holds at the states that the verifier reaches is
a premise: it is shown of no family here. No example at the release's own values: the small state is
hand-made; no row is pending at it, so the second half of `pileWithinC` accepts idly there
(`front_facts` spends the first half alone). Who lays free0 and fvs is not said: they are any two
values at which the test on the room accepts, and the premise hpos is closed only where they are
numerals. The field mask is not spoken of. Nothing on soundness.

-/
import Johnson.Top.H0.Walk.FrameEntriesDefs
import Johnson.Desc.K13.Law.LedgersC
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open Fmt.Places (logUp)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.K13 (pileWithinC ledgersFitC indexIsC)
open VerifiableInference.Desc.K13.Law (LedgerAt LedgersFit ledgersC tableSize_mask)
open VerifiableInference.Desc.K12.Door (atFirstShapes msgShapesB msgShape_at)
open Johnson.Desc.First.Walk.Tied (leftIsB roomIsB rowsBefore)

/-- **Where the index masks' ledger has just n entries left, the message is there and has a
ledger.** -/
theorem ledger_of_left {n : ℕ} {s : S} (h : leftIsB n s = true) :
    ∃ x l, s.st.oracles[s.out.indexMasks]? = some x ∧ x.ledger = some l := by
  unfold leftIsB at h
  cases e : Johnson.Desc.First.Walk.Law.ledgerAt s with
  | none => simp [e] at h
  | some l =>
    have e' : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) = some l := e
    obtain ⟨x, hx, hl⟩ := Option.bind_eq_some_iff.1 e'
    exact ⟨x, l, hx, hl⟩

/-- The field left: where the test on the room accepts and the number that it names is not 0, the
index masks' ledger is not closed and has an entry left. -/
theorem left_of_room {free0 m : ℕ} {fvs : List Bool} {s : S} (h : roomIsB free0 fvs m s = true)
    (hpos : 0 < free0 - rowsBefore fvs m) : ∃ n, 0 < n ∧ leftIsB n s = true :=
  ⟨free0 - rowsBefore fvs m, hpos, h⟩

/-- The field made: where every ledger in the statement fits and the index masks' message has a
ledger, that ledger is the ledger of some number of takes. -/
theorem made_of_pile {n : ℕ} {s : S} (hp : pileWithinC s = true) (hl : leftIsB n s = true) :
    ∃ k, LedgerAt s.st s.out.indexMasks k := by
  unfold pileWithinC at hp
  rw [Bool.and_eq_true] at hp
  obtain ⟨x, l, hx, hxl⟩ := ledger_of_left hl
  exact (ledgersC s).1 hp.1 s.out.indexMasks x hx (by rw [hxl]; rfl)

/-- The field size: the index masks' message has the number ix, the listed shape at ix is sh, and
the codes are cs: so its mask table has the size of a mask table of that shape under these codes. -/
theorem size_of_shapes {ix ni k : ℕ} {M : List OracleShape} {cs : Codes} {sh : OracleShape} {s : S}
    (hk : LedgerAt s.st s.out.indexMasks k) (hix : indexIsC ix s = true)
    (hsh : atFirstShapes M s = true) (hcs : s.st.codes = cs) (hM : M[ix]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni) :
    tableSize s.st s.out.indexMasks .mask = ni := by
  obtain ⟨x, _, hx, _, hm, _⟩ := hk
  have ei : s.out.indexMasks = ix := eq_of_beq hix
  have ho : s.out.indexMasks < s.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  have e := msgShape_at (show msgShapesB M s.st = true from hsh) s.out.indexMasks ho
  rw [hx, ei, hM] at e
  have es : x.shape = sh := Option.some.inj e
  rw [tableSize_mask hx hm, es, hcs]
  exact hni

/-- **The three fields left, made and size at one state.** free0, fvs: any two values at which the
test on the room accepts (meant: how many entries the index masks' fresh ledger has; segment by
segment, whether it leaves a row on the committed table); m: the merge's segment; ix: the listed
number of the index masks' message; M: the listed shapes of the chain's oracle messages; cs: the
listed codes. -/
theorem front_facts {free0 m ix ni : ℕ} {fvs : List Bool} {M : List OracleShape} {cs : Codes}
    {sh : OracleShape} {s : S} (hroom : roomIsB free0 fvs m s = true)
    (hpos : 0 < free0 - rowsBefore fvs m) (hpile : pileWithinC s = true)
    (hix : indexIsC ix s = true) (hsh : atFirstShapes M s = true) (hcs : s.st.codes = cs)
    (hM : M[ix]? = some sh)
    (hni : 2 ^ (logUp sh.maskRows + logUp (cs.mask.getD sh.maskCode default).ell) = ni) :
    (∃ n, 0 < n ∧ leftIsB n s = true) ∧ (∃ k, LedgerAt s.st s.out.indexMasks k) ∧
      tableSize s.st s.out.indexMasks .mask = ni := by
  obtain ⟨k, hk⟩ := made_of_pile hpile hroom
  exact ⟨left_of_room hroom hpos, ⟨k, hk⟩, size_of_shapes hk hix hsh hcs hM hni⟩

/-! ## Small values: the premises can be met together, and each test can reject -/

namespace FactsToy

/-- The one shape: one mask row, one answer to its OOD sample. -/
def sh1 : OracleShape := { maskRows := 1, maskCode := 0, answers := 1 }

/-- The codes: one mask code, of 256 places. -/
def cs1 : Codes := { mask := #[{ logN := 10, ell := 256, r := 1 }] }

/-- A verifier's state between two segments, without a mark: one oracle message, of that shape, with
the ledger l; the index masks' message is message number ix. -/
def stateOf (ix : ℕ) (l : Ledger) : S :=
  { S.blank with
    st := { codes := cs1, oracles := #[{ shape := sh1, ledger := some l }] }
    out := { indexMasks := ix }
    failed := none }

/-- Twelve of 255 entries are taken, 243 are left, and the search goes on at number 12. -/
def s12 : S := stateOf 0 { next := 12, left := 243, rows := 1, logRows := 0 }

/-- Twenty-five segments; every other one, from the first on, leaves a row. -/
def fvs25 : List Bool := (List.range 25).map fun i => i % 2 == 0

theorem rows_before : rowsBefore fvs25 24 = 12 := by decide +kernel

/-- **All premises of `front_facts` are met at the small state, and it bears no mark.** -/
theorem premises_met :
    roomIsB 255 fvs25 24 s12 = true ∧ 0 < 255 - rowsBefore fvs25 24 ∧ pileWithinC s12 = true ∧
      indexIsC 0 s12 = true ∧ atFirstShapes [sh1] s12 = true ∧ s12.st.codes = cs1 ∧
      [sh1][0]? = some sh1 ∧
      2 ^ (logUp sh1.maskRows + logUp (cs1.mask.getD sh1.maskCode default).ell) = 256 ∧
      s12.failed = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl⟩ <;> decide +kernel

/-- So the three facts hold there, with 256 for the table's size. -/
theorem facts_there :
    (∃ n, 0 < n ∧ leftIsB n s12 = true) ∧ (∃ k, LedgerAt s12.st s12.out.indexMasks k) ∧
      tableSize s12.st s12.out.indexMasks .mask = 256 :=
  front_facts premises_met.1 premises_met.2.1 premises_met.2.2.1 premises_met.2.2.2.1
    premises_met.2.2.2.2.1 premises_met.2.2.2.2.2.1 premises_met.2.2.2.2.2.2.1
    premises_met.2.2.2.2.2.2.2.1

/-- NEGATIVE TEST: one entry more is left: the test on the room rejects. -/
theorem room_rejects_left :
    roomIsB 255 fvs25 24 (stateOf 0 { next := 12, left := 244, rows := 1, logRows := 0 }) =
      false := by
  decide +kernel

/-- NEGATIVE TEST: the ledger is closed: the test on the room rejects. -/
theorem room_rejects_closed :
    roomIsB 255 fvs25 24
      (stateOf 0 { next := 12, left := 243, rows := 1, logRows := 0, closed := true }) = false := by
  decide +kernel

/-- NEGATIVE TEST: the closed premise fails where as many segments bear as there are entries. -/
theorem no_room_left : ¬ 0 < 12 - rowsBefore fvs25 24 := by decide +kernel

/-- NEGATIVE TEST: the search stands one number too far: the test on the ledgers rejects. -/
theorem pile_rejects_next :
    pileWithinC (stateOf 0 { next := 13, left := 243, rows := 1, logRows := 0 }) = false := by
  decide +kernel

/-- NEGATIVE TEST: another number of the index masks' message. -/
theorem index_rejects : indexIsC 1 s12 = false := by decide +kernel

/-- NEGATIVE TEST: the listed shape has two mask rows. -/
theorem shapes_reject : atFirstShapes [{ sh1 with maskRows := 2 }] s12 = false := by decide +kernel

end FactsToy

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.ledger_of_left
#print axioms VerifiableInference.Desc.First.MergeLaw.left_of_room
#print axioms VerifiableInference.Desc.First.MergeLaw.made_of_pile
#print axioms VerifiableInference.Desc.First.MergeLaw.size_of_shapes
#print axioms VerifiableInference.Desc.First.MergeLaw.front_facts
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.rows_before
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.premises_met
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.facts_there
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.room_rejects_left
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.room_rejects_closed
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.no_room_left
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.pile_rejects_next
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.index_rejects
#print axioms VerifiableInference.Desc.First.MergeLaw.FactsToy.shapes_reject
