-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/Statements.lean: THE STATEMENTS, AND NO PROOF: "WHAT IS OPEN ACROSS K4's
SUB-PROTOCOL RIDES BACK OVER ITS YES, EACH ITEM AT ITS OWNER's OWN SENTENCE". Definitions alone:
which sorts of item ride at K4's row of the table of joints, and, a sort a sentence, what is owed
for it. The proofs stand in the files beside (Riders/…), one a sentence.

WHO SPENDS THEM: the line same of `K4Riders` (K4RidesFenced.lean) at the table's one composed
filling (Johnson/Desc/Sound/MgAll.lean): under `K4Riders` what rides past K4's sub-protocol goes
back from behind an accept to in front (`k4_rides_fenced`): one of the ties of K4's kind at the
table.

WHICH SORTS RIDE (by reading the table's rows, Johnson/Desc/First/Borders.lean: `start`, `segRow`;
the test `k4RidersFit` says it with code). In front of piece 3 of a feed-forward segment m there are
open: from the start: "no mark" · pinW · pile · of every segment j the four parts of its relation
that no sub-protocol has closed yet · pinI (since the first sending) · from segment m's first
sub-protocol: pin m 0 and the rows' classes sample 0, and, at m > 0, carried and position · from the
lookup on the calls: formsT m 2 "objects" and the three worth m 2. K4's ROW CLOSES OR READS: constr
m idn · the three worth m 2 · pin m 0 · pinW · constr m small · pinI · "no mark". SO THERE RIDE, AND
NO OTHER: (1) pile (2) constr j p at every LATER segment j > m, p not the digits' part (3) row m c
at the classes named (4) formsT m 2 "objects". STRUCK, WITH WHY: pin · pinKept · pinV · tie · forms
· worth · wo · totalB · total · carry · pileOne · wrow: none is open in front of K4's sub-protocol
and outside its row: each earlier segment's items are closed by its own sub-protocols and by the
next segment's first.

THE SENTENCES, EACH HELD AGAINST ITS OWNER's TEXT.
  `RidersAre`: under the test and the table's two tests on its rows, an item that rides has
    `riderSort`.
  `RidesPile`: the index's layer's sentence is "every row of S.rows holds of the witness as rw reads
    it" (`RowsTrue`): owed: IN A FEED-FORWARD SEGMENT `Rest` KEEPS S.rows. It reads out.pending
    there: kept. (rw, a letter that may read the verifier's state, is the caller's line.)
  `RidesRow`: the rows' layer's sentence (`rowSays N (wordsAtFirst arr)`) reads the state's st and
    book alone: kept by `Rest`: it rides at every class, both ways.
  `RidesConstr`: the model's relation's layer's sentence (`P5J.constrQAt`): it reads the layer's
    decoder and its reader of the request, and, at the head's segment, the letter headPart; the
    digits' part does not ride.
  formsT m 2 "objects": `K4Riders.objects` as it stands: THE ONE RIDER WHOSE SENTENCE READS THE
    LEDGER, which K4's accept turns: its statement at the runs' forms' layer's sentence is owed in a
    file of its own.

Limits. SENTENCES: NOTHING IS PROVED HERE. "Which sorts ride" is by reading until `k4RidersFit` has
been evaluated at the real lists. The public items that are open across K4 (the lines pub and pubP
of `K4Keeps`) are not in this file. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.
-/
import Johnson.Road.K4.K4RidesFenced
import Johnson.Desc.First.K4PlanFit
import Johnson.Desc.Sound.SpineList
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Place Strs Wit)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item RowClass Numbers start openSets readsOpen
  rowSays wordsAtFirst)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (insQ outsQ openAfter insL rowsApart MsgT)

/-- The sorts of item that ride at K4's row, at a feed-forward segment m. -/
def riderSort (m : ℕ) : Item → Bool
  | .pile => true
  | .constr j p => decide (m < j) && !decide (p = .lookDigits)
  | .row j c => j == m && (decide (c = .carried) || decide (c = .position) || decide (c = .sample
  0))
  | .formsT j k r => j == m && k == 2 && r == "objects"
  | _ => false

/-- A TEST ON THE TABLE: at every place of K4's, whatever is open in front and is neither closed nor
read by the row is of these sorts. -/
def k4RidersFit (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | none => true
    | some pl =>
      !isK4At links pl ||
        ((openSets links ps (start links))[k]?.getD []).all fun i =>
          (insL links ps k).contains i || riderSort (pl.link.getD 0) i

/-- Under the three tests, an item that rides at K4's place has `riderSort`. -/
def RidersAre : Prop :=
  ∀ (links : List ModelPart) (ps : List Place) (k m : ℕ) (pl : Place), AtK4 links ps k m pl →
    k4RidersFit links ps = true → readsOpen links ps (start links) = true →
    rowsApart links ps = true → ∀ i,
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    riderSort m i = true

/-- In a feed-forward segment what K4's accept leaves keeps the pending rows. -/
def RidesPile : Prop :=
  ∀ (s s' : S) (a : LayOwn), Rest s s' → s.here = .lay a → s'.rows = s.rows

/-- The rows' layer's sentence says one thing at two states with `Rest`, whatever the strings. -/
def RidesRow : Prop :=
  ∀ (P Cells Tok : Type) (N : Numbers) (arr : ℕ → ℕ → ℕ) (m : ℕ) (c : RowClass) (Z : P) (s s' : S)
    (y y' : Strs) (w : Wit Cells Tok MsgT), Rest s s' →
    (rowSays N (wordsAtFirst arr) m c (Z, s') y' w ↔ rowSays N (wordsAtFirst arr) m c (Z, s) y w)

/-- The index of the model's commitment (its owner's own type). -/
abbrev IdxK : Type := open Inst.Model Inst.Model.All in Cm.Idx

/-- The model's relation's layer's sentence goes back from (b, y') to (a, y), where its readers give
one thing. -/
def RidesConstr : Prop :=
  ∀ (X : Verify.Public) (P W : Type) (rows cols hd : ℕ)
    (put : P5J.TReq → Fin Inst.Model.ppref.V → P5J.TReq) (H : P5J.HidAt X P W rows cols)
    (headPart : P5J.TPart → IdxK → P × S → Strs → W → Prop)
    (digitsPart : ℕ → P × S → Strs → W → Prop) (k : ℕ) (p : P5J.TPart) (a b : P × S)
    (y y' : Strs) (w : W), H.dec a y = H.dec b y' → H.req a = H.req b →
    (k = hd → ∀ i, headPart p i b y' w → headPart p i a y w) →
    (p = .lookDigits → digitsPart k b y' w → digitsPart k a y w) →
    P5J.constrQAt hd put H headPart digitsPart k p b y' w →
    P5J.constrQAt hd put H headPart digitsPart k p a y w

end OnBytes.Road.K4.Riders
