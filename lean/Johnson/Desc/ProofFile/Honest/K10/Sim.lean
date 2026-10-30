-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Sim.lean: the closing of a segment (K10): the spender's half. The row's form is the
total one (tot = true). The lot that lays it: `seatLotT` (Honest/K10/SeatLotT.lean). The form tot = false is not the
row's; wherever below tot = false, `closeOnAt`, `closeOn false` or (4') is spoken of, that other form is meant.
Definitions; seven statements, not one of which is proved in this file ((3a): Honest/K10/SimMap.lean; (5), and (3c), (2)
from (3b): Honest/K10/SimLaws.lean; (3b), and so (3c) and (2), at tot = true: Honest/K10/SimSent.lean; (4''), (4'), and
(3b) at tot = false: nowhere: no statement of this library concludes `CloseAskPublic`); nine small general lemmas,
proved. What the simulator's form is handed: by the frame's type the public part of the input, what stands in front, the
challenges, the positions, coins of its own; of these it reads its coins alone (`fun _ _ _ _ c`); and, of the place, k
and the address, off the plan: public. A part, the form of a simulator beside it, the member that the two make, and, as
definitions of type Prop, what would have to be shown of them in the frame's letters (`Good.exact`, `Good.fresh`,
Honest/Side.lean). What would follow from these statements is not said here. None of the library's goals.

The run that is spent is lent. Its 2 k + 1 coins, under the name `runName foldMaskRun (closeAddr P) "fold"`, are coins
of the part that sends the closing's fresh mask: by the page named below a first sending (kind K1) at the first
segment, a code switch (kind K2) at the others. (1) to (4'') are the spender's half alone: the
owner's sentence, `Good.fresh` at that sender for this part, is not here: at public files in scope
at which the gate accepts, at what the maker returns there, it is `owner_fresh_at_return`
(AtFullSide/K1/GoodAtReturn.lean) at K1's 52 senders of the first chain and the clause
`SidesMeetGood` of `simulatorAtTheBase` (AtFullSide/K2/SimulatorAtTheBaseProof.lean) at the code
switches, each with its file's limits. Without it the spender's half says nothing of a run. Who
carries the run behind this part, by the texts of the two kinds' honest parts (by reading; no
theorem):
the run's coins are coins of the fresh mask's message, and all coins of that message are carried by every code switch at
a later link (Honest/K2/Half.lean: `switchPlaces`: front := all that the segments in front have sent, `frontOf`, the
fresh masks among them) and by every closing of a later segment (Honest/K10/BorneAt.lean; `groupRowsOf`,
Honest/K2/Closing.lean: "those of all messages of the segments before, fresh masks among them"). Behind the last
closing: `switchPlaces` lays a place of the kind K2 that bears no link's number at the number of links, with all
segments in front; that the plan has such a place (25 switches at 25 links) is the word of those who wrote the plan; it
is tied to the plan's table of steps by no theorem. The description's own text has it: the kinds of the blocks behind
the last segment begin with K2, then K12 (`backKinds`, Johnson/Desc/First/Driver/Chain.lean). That this K2 carries the
run is `switchPlaces`' text above; by that page both parts of that K12 carry it behind: of K12 nothing has been
stated here. The count, at equality: 2 k + 1 coins are spent; 1 + 2 k elements are sent. (3a), a statement, says
that the map from the coins to what is sent of them and the map back undo each other; which coin stands with the factor
1 under which sent element is said in `runBackN`'s docstring alone. Of the zeros behind the 2 k + 1 in the sender's
table nothing is said here: they are the sender's. The same coins elsewhere, as that page lists it. Of these coins
a run of the protocol shows more than this part sends: the fresh mask's table is made of them by its sender, is
committed, and its symbols are shown at the positions that are read; the code switch behind lays that table's folded row
into the message that it sends; from there on they go as data into what later parts send. Of none of the three does any
statement here speak. What has been shown. The data read nothing of the part's own earlier rounds: `cut_own`,
`ask_own_free`, proved. That nothing shown in front of the part hangs on the run is not stated here: it is a
sentence on the book (no other part in front than the sender is handed a coin of the run) and on the sender (no answer
reads the fresh mask); it is not stated here; its place is where the book is made and where the
sender is written, beside the sender's `fresh`: "no item in the clear of the sender's rounds reads a
coefficient". Where columns are handed, what is shown in front of the part spans the columns opened
so far. So the sentence is also one on the description: that no column of the fresh
mask's table, whose entries are made of the run's coins, is opened in front of the part. That too is not stated here.
The carried runs. The sentence (2) stands at every
fixed value of the carried runs, and its right side is handed none of them. On the carried runs there is no statement
apart from (2), (4') and (4''). Where this text parts from the page from which it is typed (a page of this
project on the forms of simulators, which is not in the repository: its form of a fold). (i) There the part is total and
the letter On asks nothing. Here both forms are typed, by one Bool: tot = true: that form, the row's: no refusal; On
asks nothing. tot = false, not the row's: the part refuses aloud where data do not fit, and On is `closeOnAt`. (ii)
There the sentence stands at a seated member, under three clauses on what the frame's play reads; here at the kind's own
declared rounds (`closeRounds`). (iii) There the tables' share of what is sent is a function that is never handed the
run; here run and tables are laid into one value (`FoldAsk`) and handed to the shared fold's words: that the tables'
share does not hang on the run is a statement, (3b), not the type's. The page's letters k ≥ 1, h ≤ k are `closePlan`.
Into which values a default can flow. (a) `bareAsk`'s empty tables: into the tables' share of each sent element: at a
stand at which no statement is at hand; at tot = true also wherever `closeAskAt` refuses, whatever it refuses on: so
there, by type, whether the default is laid can hang on the input and on a carried coin's value, not on what is public
or was heard alone: the job's rows are handed both; and since `stAt` is handed the input, whether a statement is at
hand, and which, can, by type, hang on the input too, in both forms: and with it the tests in front of the rows and the
data's coefficients and layout. That the end does not is (4''), a statement of a job: whether the data are made is a
function of the input's public part and of what was shown and heard; (4'') binds no value: that the statement is one is
a further law on a job, defined nowhere in this library (near it: `jobAt_of_own`, Honest/K10/Reads/Door.lean). This form
has no named public premise: by type it can default on more than what is public or was heard; that it does not at the
lot's job is (4'') there (`SeatedAskPublic`, Honest/K10/SimSeat.lean): no statement of this library concludes it. (b) A
0 for a challenge that lacks or drew no element (`headD`; the frame's `drawnE`; `epsOf`): into the factor and the
challenges; at tot = false `closeAskAt` has refused in front of it. (c) Job.lean's zeros at a number that is no member's
and beyond a message's rows, its default code, its "not kept" beyond a list; the shared words' 0 beyond an array's end:
into entries of the tables, or into a refusal (three theorems on the first: Honest/K10/AskLaw.lean). (d) `atN`'s 0
beyond the count: into `runSent`'s and `runBack`'s values, if a number from 2 k + 1 on were read: none is, by a program
outside Lean at k ≤ 12; by no theorem. None into the run's place, by reading: the run is typed at its number, in the
part, in the simulator's form and in the statements. Premises by name. `closePlan`: public: the kind's own `planOk`
(`closePlan_iff`, proved); the page's letters; not all of it is spent (h ≤ k nowhere; 1 ≤ k by (3a) and (3b) alone: so
in Lean: Honest/K10/SimMap.lean, SimSent.lean); owed by whoever lays the places; shown met at no policy file. `closeOn
false` (not the row's form): owed by this kind, at the stands of a thread. By type it can hang on the input and on a
carried coin's value (the job's rows are handed both; `stAt` the input); that it hangs on no carried coin's value is
(4'), a statement of a job. In (5): no entry of the book lets any part spend a coin of this part's (owed where the book
is made; the part has no coin; shown met at no policy file). Stops: none: both of the part's stops are the constant
"nothing"; a refusal is no stop: at tot = false it stands in On. At tot = true the frame's "no part is at fault" is met
for nothing at this part: what it used to guard moves to the verifier's yes: that the data come, and are the true
tables, at the stands of a thread is owed there.

  `closePlan`, `bareAsk`, `spentRun`, `askOr`, `foldShellT`   the part, cured: as `foldShell` (Honest/K10/Job.lean),
                   but where the data are nothing it sends what the fold's words say at empty tables and the run: the
                   coins are laid at every stand at which it sends
    `CloseJob.over`, `lift_is`, `seat_is`   a job carried over to a wider input; proved: the part, lifted as the
                   kind's seat lifts it, is the part at the carried-over job
  `layF`, `closeTell`, `closeSim`   (1) the form of the simulator: 2 k + 1 coins of its own, laid as they are into the
                   rounds' shapes: none, one, then k times two; no column
  `closeRounds`, `closeAt`   the literal member: number 0; the kind's 2 + k declared rounds, none with an oracle
                   message; the part; the simulator's form. Proved: `closeRounds_is`: these are the kind's own
                   block's; `moves_len`, `members_is`: it is the one member of a side with that row and such a block
    `closeOnAt`, `closeOn`, `closeBud`   (4) the letters On and bud. At the row's form On asks nothing (its premise is
                   "true = false"). `closeOnAt` (the other form's): the making of the closing's data does not refuse (it
                   may yield nothing): at the stand in front of the part, at the carried runs, at every run that could
                   be spent and every challenge that "BAT" can draw. bud: True: the part sends no table
            `CloseOnFree` (4') (the other form's) whether the making of the data refuses hangs on no value of a carried
            coin
  `askVerdict`, `CloseAskPublic`   (4'') whether the data are made (a refusal, nothing, or the data) is a function of
                   the input's public part and of what was shown and heard: it hangs on nothing else of the input, on no
                   carried coin's value and on no coin of the run: which end, no value: the law that the job's statement
                   in front of "BAT" is one at the two inputs goes with it. "What was shown" is a `Seen`: the rounds
                   and, where they are handed, the columns opened so far, a stored table's among them; in a real run
                   these depend on the index and on coins. On that (4'') says nothing.
  `ExactAt`, `FreshAt`   the frame's two fields at one member. `FreshAt` is a copy; proved: `freshAt_of_good`: it is
                   what the frame's own field gives. `ExactAt` is `Good.exact`'s sentence without its premise on
                   `m.opened`: it is asked at every value of that field; the frame's field gives its equation only where
                   that premise holds. The field's own form: `ExactMemberAt`; from `Good pre` to it: `members_of_good`
                   (Honest/Small/Field.lean)
  `CloseExact`    (2) `Good.exact`'s sentence without its premise on `m.opened`, at the literal member, of any side
  `CloseFresh`    (5) `Good.fresh`'s own sentence at the literal member, of any side, under the premise on the book.
                   It reads nothing of the kind
  `runSent`, `runBack`, `RunOneToOne`   (3a) over any commutative ring: the map from the run's 2 k + 1 coefficients,
                   in the book's order, to 1 + 2 k values in the order of sending; a map back, written out; the
                   statement: each undoes the other
  `CloseSentIs`   (3b) at everything else fixed, what the member shows is: `runSent` of the run, plus what
                  "FOLD epsilon" drew times values that do not hang on the run, the first of them 0
  `CloseOneToOne` (3c) at everything else fixed there is an equivalence of the coins over which the part's side of the
                   sentence is drawn with the simulator's coins, under which what the member shows is what the
                   simulator's form lays
  `cut_own`, `ask_own_free`   proved: at the fold's move number n the closing's data do not read the last n + 1 rounds
                   shown
  `atN`, `phiB`, `sumB`, `runSentN`, `runBackN`, `runE`, `epsOf`, `closePlan_iff`   the pieces of these; five lines of
                   the command `#guard` hold the two maps at written numbers

Limits. Of the seven, statements alone, in this file. The statements that bind a face, (2), (3b), (3c), (4''), (5), bite
only at a job typed at a face's input: the frame has two faces, at its own two types of input; at any other type they
are met for nothing. The lot's job (`jobAt`, Honest/K10/SeatLot.lean) is typed at the small record `CloseIn` and seated
by a lift: `CloseJob.over` carries a job over to the face's input; proved: `lift_is`, `seat_is`: the part so lifted is
the part at the carried-over job: so the statements are to be taken at `(jobAt …).over inOf`. `foldShellT true` is laid
in a lot by `seatLotT` (Honest/K10/SeatLotT.lean); `seatLotR` (SeatLot.lean), with the older caller, is not taken away
and is marked as not to be laid; no definition and no maker of a description calls either lot. `seatLotC`
(Honest/K10/SeatLotC.lean) lays the same part at the closings alone, and `closeLotAt` (Honest/AtPureWiderK10.lean) lays
its halves in a filling. `members_is`'s premise on the block, and `Side.fits`, in scope, at `OnBytes.secondHashFunction`, at the c
of `IM.Open`: `member_at_scope` (Honest/K10/SimLot.lean). Nothing ties the run's order here to the sender's table. The
challenges are fixed in every statement. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Words
import Johnson.Desc.ProofFile.Honest.K10.Seat
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E zeroE)
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par entries)

variable {S Cl V W X Pb : Type}

/-! ## The part, cured, in two forms (the row's: tot = true) -/

/-- **The public premise on the place**: the kind's own test on the plan (`planOk`,
Johnson/Desc/First/Close/Kind.lean). -/
def closePlan (P : Par) : Prop := 1 ≤ P.k ∧ P.h ≤ P.k

theorem closePlan_iff {Cl' : Type} (P : Par) :
    closePlan P ↔ ((First.Close.kind (Cl := Cl')) P).planOk = true := by
  show _ ↔ (decide (1 ≤ P.k) && decide (P.h ≤ P.k)) = true
  simp [closePlan]

/-- The fold's data at empty tables: of the closing nothing but the two numbers and the run. -/
def bareAsk (P : Par) (u : Fin (2 * P.k + 1) → E) : FoldAsk :=
  { k := P.k, h := P.h, c := #[], d := #[], m := #[], mu := #[], keptV := zeroE, w := u }

/-- The run that is spent, as `closeAskAt` reads it. -/
def spentRun (J : CloseJob W) (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) :
    Fin (2 * J.pub.par.k + 1) → E :=
  let u : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit := c.2.1
  fun i => E.ofTriple (OnBytes.Slice.ofE (u.1.e i))

/-- The closing's data at the fold's move number n, in the two forms. tot = false (not the row's): `closeAskAt` as it
is: its refusals stay. tot = true (the row's): no refusal: where `closeAskAt` refuses, nothing, as where no statement
is at hand. -/
def askOr (tot : Bool) (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (s : Seen) (t : State W X) :
    Except String (Option (FoldAsk × List E)) :=
  if tot then .ok (closeAskAt J n c s t).toOption.join else closeAskAt J n c s t

/-- **The caller, cured**: `foldShell` (Honest/K10/Job.lean) with one turn: where the data are nothing, the move sends
what F says at `bareAsk` and the run; and at tot = true a second: `askOr`'s. -/
def foldShellT (tot : Bool) (J : CloseJob W) (F : FoldWords) : Part V W X :=
  { takes := ⟨0, 0⟩, spends := closeSpends J.pub.par, carries := closeCarries J.pub
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      ⟨fun c s t => (askOr tot J 0 c s t).map fun
          | some y => sayE [F.sigma y.1]
          | none => sayE [F.sigma (bareAsk J.pub.par (spentRun J c))], fun t => t.own⟩ ::
      (List.range J.pub.par.k).map fun j =>
        ⟨fun c s t => (askOr tot J (j + 1) c s t).map fun
            | some y =>
              let q := F.round y.1 (y.2.headD zeroE) (y.2.drop 1)
              sayE [q.1, q.2]
            | none =>
              let g := drawnE (t.lately (j + 1))
              let q := F.round (bareAsk J.pub.par (spentRun J c)) (g.headD zeroE) (g.drop 1)
              sayE [q.1, q.2], fun t => t.own⟩ }

/-- **A job carried over to a wider input**: its rows and its `stAt` read the input through inOf. -/
def CloseJob.over {W' : Type} (inOf : W' → W) (J : CloseJob W) : CloseJob W' :=
  { pub := J.pub, stAt := fun w => J.stAt (inOf w), rows := fun w => J.rows (inOf w) }

/-- **The part, lifted as the kind's seat lifts it, is the part at the carried-over job.** -/
theorem lift_is {V' W' X' : Type} (tot : Bool) (J : CloseJob W) (F : FoldWords) (inOf : W' → W) :
    ((foldShellT tot J F : Part Unit W Unit).lift (fun _ => ()) inOf (fun _ => ()) fun x _ => x :
      Part V' W' X') = foldShellT tot (J.over inOf) F := by
  simp only [Part.lift, foldShellT, List.map_cons, List.map_map]
  rfl

/-- So at the kind's seat (`seatFold`, Honest/K10/Seat.lean). -/
theorem seat_is {W₀ Rc Xi Tr X' : Type} (tot : Bool) (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (Jof : ClosePub → CloseJob CloseIn) (Z : ClosePub) :
    (seatFold (X := X') inOf (fun Z => foldShellT tot (Jof Z) foldWords) Z) =
      foldShellT tot ((Jof Z).over inOf) foldWords :=
  lift_is tot (Jof Z) foldWords inOf

/-! ## (1) The form of the simulator -/

/-- 1 + 2 k elements laid into the rounds' shapes: none, one, then k times two; no column. -/
def layF (k : Nat) (f : Fin (2 * k + 1) → Cb.Gl.E) : List Shown :=
  let e : Fin (2 * k + 1) → Fmt.ItemValue := fun i => .e (E.ofTriple (OnBytes.Slice.ofE (f i))).triple
  ⟨[], []⟩ :: ⟨[e ⟨0, by omega⟩], []⟩ ::
    List.ofFn fun j : Fin k =>
      ⟨[e ⟨1 + 2 * j.1, by have := j.2; omega⟩, e ⟨2 + 2 * j.1, by have := j.2; omega⟩], []⟩

/-- What the simulator's form lays: its coins as they are. -/
def closeTell (k : Nat) (c : Cs ⟨0, 2 * k + 1⟩) : List Shown := layF k c.e

/-- **The form of the simulator.** -/
def closeSim (P : Par) : Sim Pb :=
  { addr := closeAddr P, takes := ⟨0, 2 * P.k + 1⟩, tell := fun _ _ _ _ c => some (closeTell P.k c) }

/-! ## The literal member -/

/-- The kind's declared rounds, none with an oracle message. -/
def closeRounds (P : Par) : List (Fmt.DeclaredRound × List Oracle) :=
  (entries P).map fun e => ({ entry := e }, [])

/-- They are the kind's own block's rounds, each with its list of oracle messages. -/
theorem closeRounds_is {Cl' : Type} (P : Par) :
    ((First.Close.kind (Cl := Cl')) P).rounds.zip ((First.Close.kind (Cl := Cl')) P).oracles =
      closeRounds P := by
  show ((entries P).map fun e => ({ entry := e } : Fmt.DeclaredRound)).zip
    ((entries P).map fun _ => ([] : List Oracle)) = _
  rw [List.zip_map']
  rfl

/-- **The literal member**, in the two forms: the row's is tot = true. -/
def closeAt (tot : Bool) (J : CloseJob W) : Member V W X Pb :=
  ⟨0, closeRounds J.pub.par, closePart (foldShellT tot J foldWords), closeSim J.pub.par⟩

/-- The part has a move for each declared round. -/
theorem moves_len (tot : Bool) (J : CloseJob W) :
    (closePart (V := V) (X := X) (foldShellT tot J foldWords)).moves.length =
      (closeRounds J.pub.par).length := by
  show ((closeBatPart (V := V) (W := W) (X := X)).moves.map _ ++
    (foldShellT (V := V) (X := X) tot J foldWords).moves.map _).length =
      ((entries J.pub.par).map _).length
  rw [List.length_append, List.length_map, List.length_map, List.length_map]
  simp only [closeBatPart, foldShellT, entries, List.length_cons, List.length_map,
    List.length_range, List.length_replicate, List.length_nil]
  omega

/-- **It is the one member of a side** whose row is the part with the simulator's form, and whose block has the kind's
rounds and oracle messages. -/
theorem members_is (tot : Bool) (J : CloseJob W) (σ : Side S Cl V W X Pb)
    (hr : σ.row = [(closePart (foldShellT tot J foldWords), closeSim J.pub.par)])
    (hb : σ.block.rounds.zip σ.block.oracles = closeRounds J.pub.par) :
    σ.members = [closeAt tot J] := by
  unfold Side.members
  rw [hr, hb]
  show [(⟨0, (closeRounds J.pub.par).take _, _, _⟩ : Member V W X Pb)] = _
  rw [moves_len, List.take_length]
  rfl

/-! ## (4) On and bud -/

/-- The making of the closing's data does not refuse (it may yield nothing, where no statement is at hand): at the stand
m in front of the part, at the carried runs, at every challenge that fits "BAT"'s declared round, at every run: the run
is bound here, so the sentence reads no coin that is spent. -/
def closeOnAt (J : CloseJob W) (ca : CsAll (closeCarries J.pub)) (m : Mid W X) : Prop :=
  ∀ (x : Fmt.Drawn) (u : Fin (2 * J.pub.par.k + 1) → E),
    drawsFit ((closeRounds J.pub.par).map (·.1) |>.take 1) [x] = true →
    (closeAsk J m.st.input m.shown m.st.heard x u ca).toOption.isSome = true

/-- **The letter On**, in the two forms: tot = true (the row's): it asks nothing. tot = false: `closeOnAt`, under "the
member's carried runs are the job's": at a member with other carried runs it asks nothing. -/
def closeOn (tot : Bool) (J : CloseJob W) :
    (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop :=
  fun u ca m _ => tot = false → ∀ h : u.part.carries = closeCarries J.pub, closeOnAt J (h ▸ ca) m

/-- **The letter bud**: the part sends no table. -/
def closeBud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop := fun _ _ _ => True

/-- **(4') whether the making of the data refuses hangs on no value of a carried coin.** Of the form tot = false: not
wanted at the row's. By type it could: the job's rows are handed the carried runs. A statement, of a job; not proved. -/
def CloseOnFree (X : Type) (J : CloseJob W) : Prop :=
  ∀ (ca ca' : CsAll (closeCarries J.pub)) (m : Mid W X), closeOnAt J ca m ↔ closeOnAt J ca' m

/-- What becomes of the making of the data: no value where `closeAsk` refuses; "no" where it yields nothing (no
statement is at hand); "yes" where it yields the data. -/
def askVerdict (J : CloseJob W) (w : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u : Fin (2 * J.pub.par.k + 1) → E) (ca : CsAll (closeCarries J.pub)) : Option Bool :=
  (closeAsk J w seen front x u ca).toOption.map (·.isSome)

/-- **(4'') whether the data are made is a function of what is public, shown and heard**: at two inputs with one public
part (the frame's `Face.pub`), at any two values of the carried runs and any two runs: one verdict. A statement, of a
job typed at a face's input, at that job as it is laid: what its two fields close over no type says. No statement of
this library concludes it, at a letter J or at the seated job, and none takes it as a premise. Near it: `verdict_run`
(Honest/K10/SimPlay.lean): one verdict at any two runs, all else the same; `closeAsk_of_job`
(Honest/K10/Reads/Door.lean): at two inputs at which the job's `stAt` and `rows` are the same, at one run and one value
of the carried runs. It binds which end is taken, no value: that the job's statement in front of "BAT" is one at the two
inputs is a further law, which bears no name in this library. No premise of (2): at tot = true it is what the default's
laying hangs on. -/
def CloseAskPublic (φ : Face V W Pb) (J : CloseJob W) : Prop :=
  ∀ (w w' : W) (seen : Seen) (front : List Fmt.Drawn) (x : Fmt.Drawn)
    (u u' : Fin (2 * J.pub.par.k + 1) → E) (ca ca' : CsAll (closeCarries J.pub)),
    φ.pub w = φ.pub w' → askVerdict J w seen front x u ca = askVerdict J w' seen front x u' ca'

/-! ## The frame's two fields at one member -/

/-- `Good.exact`'s sentence at one member u, without its premise on `m.opened`: asked at every value of that field. This
`ExactAt` is the form WITHOUT the premise; `ExactMemberAt` (Honest/Small/Field.lean) is the form WITH it, which is the
field. -/
def ExactAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- `Good.fresh`'s sentence at one member u. -/
def FreshAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

section
variable {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
  {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place}
  {chain firstTree : Nat} {A B : Coins Bk → S → Mid W X → Env → Prop}
  {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
  {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}

/-- `FreshAt` is the field's: the frame's own field gives it at each member of the side. -/
theorem freshAt_of_good (g : Good pre φ σ Bk ord chain firstTree A B On bud)
    {u : Member V W X Pb} (hu : u ∈ σ.members) : FreshAt φ σ Bk ord bud u := g.fresh u hu

end

/-! ## (2), (5) The two sentences at the literal member -/

/-- **(2) `Good.exact`'s sentence without its premise on `m.opened`, at the literal member, of any side**, under the
premise on the place. A statement; not proved here. -/
def CloseExact (S Cl V X Pb : Type) (tot : Bool) (J : CloseJob W) : Prop :=
  closePlan J.pub.par → ∀ (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (chain firstTree : Nat),
    ExactAt φ σ chain firstTree (closeOn tot J) closeBud (closeAt tot J)

/-- **(5) `Good.fresh`'s own sentence at the literal member, of any side**, under one premise on the book: no entry
lets any part spend a coin of this part's. It reads nothing of the kind: under that premise the like holds of every
member. A statement; not proved here. -/
def CloseFresh (S Cl V X Pb : Type) (tot : Bool) (J : CloseJob W) : Prop :=
  ∀ (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (Bk : ProverCoinCounts) (ord : List Place),
    (∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) →
    FreshAt φ σ Bk ord closeBud (closeAt tot J)

/-! ## (3a) The map from the run to what is sent of it, over any commutative ring

The run's 2 k + 1 elements are the coefficients of a polynomial in k variables (OnBytes/Iop/Fold.lean): the sum over
l = 1 .. k of w_l (X_l) · X_(l+1) ·· X_k, with w_l (Y) = w_(l,1) Y + w_(l,2) Y², and for l = k also the constant
w_(k,0). -/

section
variable {R : Type} [CommRing R]

/-- The run by number, in the book's order: for l = 1 .. k - 1 the coefficients (l, 1), (l, 2) at the numbers 2 l - 2, 2
l - 1; then (k, 0), (k, 1), (k, 2) at 2 k - 2, 2 k - 1, 2 k. Beyond the count a 0: it would flow into `runSent`'s and
`runBack`'s values if a number from 2 k + 1 on were read: none is, by a program outside Lean at k ≤ 12; by no theorem.
It is called on the run and on the sent values alike. -/
def atN {n : Nat} (w : Fin n → R) (i : Nat) : R := if h : i < n then w ⟨i, h⟩ else 0

/-- w_l (0) + w_l (1). -/
def phiB (k : Nat) (w : Nat → R) (l : Nat) : R :=
  if l = k then 2 * w (2 * k - 2) + w (2 * k - 1) + w (2 * k) else w (2 * l - 2) + w (2 * l - 1)

/-- `sumB k w n`: of that polynomial the summands l > k - n, each with its factor X_(l+1) ·· X_k, summed over all
values 0, 1 of the variables behind number k - n. 0 at n = 0. A step to the front, to the variable l: the new summand
gives w_l (0) + w_l (1), since each of its factors X_i sums to 1; what stood is doubled, since it does not hold X_l. -/
def sumB (k : Nat) (w : Nat → R) : Nat → R
  | 0 => 0
  | n + 1 => phiB k w (k - n) + 2 * sumB k w n

/-- **What is sent of the run**, by number in the order of sending: 0: the sum over the whole cube; 2 l - 1: round l's
constant; 2 l: round l's quadratic coefficient. No challenge and no h stands in it. -/
def runSentN (k : Nat) (w : Nat → R) : Nat → R
  | 0 => sumB k w k
  | j + 1 =>
    if j % 2 = 0 then sumB k w (k - (j / 2 + 1)) + (if j / 2 + 1 = k then w (2 * k - 2) else 0)
    else if j / 2 + 1 = k then w (2 * k) else w (2 * (j / 2 + 1) - 1)

/-- `runSentN`, typed at the 2 k + 1 numbers. -/
def runSent (k : Nat) (w : Fin (2 * k + 1) → R) : Fin (2 * k + 1) → R :=
  fun i => runSentN k (atN w) i.1

/-- **The way back, written out**: each coefficient off the sent values, one of which, named here, has the factor 1 as
an integer: (l, 2) off round l's quadratic coefficient; (k, 0) off round k's constant; (1, 1) off the sum; (l, 1), l ≥
2, off round l - 1's constant. -/
def runBackN (k : Nat) (s : Nat → R) (i : Nat) : R :=
  let B : Nat → R := fun l => if l = 0 then s 0 else if l = k then 0 else s (2 * l - 1)
  if i = 2 * k - 2 then s (2 * k - 1)
  else if i = 2 * k then s (2 * k)
  else if i = 2 * k - 1 then B (k - 1) - s (2 * k) - 2 * s (2 * k - 1)
  else if i % 2 = 1 then s (2 * (i / 2 + 1))
  else B (i / 2) - 2 * B (i / 2 + 1) - s (2 * (i / 2 + 1))

/-- `runBackN`, typed at the 2 k + 1 numbers. -/
def runBack (k : Nat) (s : Fin (2 * k + 1) → R) : Fin (2 * k + 1) → R :=
  fun i => runBackN k (atN s) i.1

end

/-- **(3a) each undoes the other**, at every k ≥ 1, over every commutative ring. A statement; not proved here. -/
def RunOneToOne : Prop :=
  ∀ (R : Type) [CommRing R] (k : Nat), 1 ≤ k →
    (∀ w : Fin (2 * k + 1) → R, runBack k (runSent k w) = w) ∧
      ∀ s : Fin (2 * k + 1) → R, runSent k (runBack k s) = s

-- The definitions held at written numbers: Honest/K10/Toy.lean's, reckoned there by hand off the library's formula of
-- that polynomial: the coins 61 .. 67 at k = 3; and the way back.
#guard (List.range 7).map (runSentN (R := Int) 3 fun i => 61 + i) == [1429, 653, 62, 263, 64, 65, 67]
#guard (List.range 7).map (runBackN (R := Int) 3 fun i => [1429, 653, 62, 263, 64, 65, 67].getD i 0) ==
  [61, 62, 63, 64, 65, 66, 67]
#guard (List.range 3).map (runSentN (R := Int) 1 fun i => 5 + i) == [2 * 5 + 6 + 7, 5, 7]
#guard (List.range 3).map (runBackN (R := Int) 1 fun i => [23, 5, 7].getD i 0) == [5, 6, 7]
-- At k = 0 the two do not undo each other: why 1 ≤ k stands in (3a), and the premise on the place in (3b) and (3c)
#guard (List.range 1).map (runBackN (R := Int) 0 (runSentN 0 fun _ => 9)) != [9]

/-! ## (3b), (3c) At the literal member -/

/-- The run, off the coins over which the part's side of the sentence is drawn. -/
def runE (tot : Bool) (J : CloseJob W)
    (c : Cs (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.takes ×
      CsAll (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.spends) :
    Fin (2 * J.pub.par.k + 1) → Cb.Gl.E :=
  let u : Cs ⟨0, 2 * J.pub.par.k + 1⟩ × Unit := c.2
  u.1.e

/-- What "FOLD epsilon", the part's second round, drew; 0 where it lacks. -/
def epsOf (ds : List Fmt.Drawn) : Cb.Gl.E :=
  (((ds.drop 1).head?.bind (·.elems.head?)).map OnBytes.Slice.toE).getD 0

/-- **(3b) what the member shows is `runSent` of the run, plus what "FOLD epsilon" drew times values that do not hang on
the run**, the first of them 0: the values are named in front of the run. Under the premise on the place (`closePlan`),
the letter On (`closeOn`) and challenges that fit the declared rounds (`drawsFit`). A statement; not proved here. -/
def CloseSentIs (S Cl V X Pb : Type) (tot : Bool) (J : CloseJob W) : Prop :=
  closePlan J.pub.par → ∀ (σ : Side S Cl V W X Pb) (φ : Face V W Pb)
    (ca : CsAll (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.carries) (m : Mid W X)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
    closeOn tot J (closeAt tot J) ca m front →
    drawsFit ((closeAt (V := V) (X := X) (Pb := Pb) tot J).rounds.map (·.1)) ds = true →
    ∃ q : Fin (2 * J.pub.par.k + 1) → Cb.Gl.E, q ⟨0, by omega⟩ = 0 ∧
      ∀ c, σ.shows φ (closeAt tot J) (c.1, c.2, ca) m ds asks =
        some (layF J.pub.par.k fun i => runSent J.pub.par.k (runE tot J c) i + epsOf ds * q i)

/-- **(3c) at everything else fixed: an equivalence of the coins on the part's side with the simulator's coins, under
which what the member shows is what the simulator's form lays.** Under the same three premises as (3b). A statement; not
proved here. -/
def CloseOneToOne (S Cl V X Pb : Type) (tot : Bool) (J : CloseJob W) : Prop :=
  closePlan J.pub.par → ∀ (σ : Side S Cl V W X Pb) (φ : Face V W Pb)
    (ca : CsAll (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.carries) (m : Mid W X)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))),
    closeOn tot J (closeAt tot J) ca m front →
    drawsFit ((closeAt (V := V) (X := X) (Pb := Pb) tot J).rounds.map (·.1)) ds = true →
    ∃ e : (Cs (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.takes ×
        CsAll (closeAt (V := V) (X := X) (Pb := Pb) tot J).part.spends) ≃ Cs ⟨0, 2 * J.pub.par.k + 1⟩,
      ∀ c, σ.shows φ (closeAt tot J) (c.1, c.2, ca) m ds asks = some (closeTell J.pub.par.k (e c))

/-! ## Two general lemmas: what the closing's data read of the rounds shown -/

/-- The cut takes the last n + 1 rounds off. -/
theorem cut_own (n : Nat) (a b : List Fmt.RoundView) (o : Option (List OpenedColumn)) (t : State W X)
    (hb : b.length = n + 1) : (closeCut n ⟨a ++ b, o⟩ t).1 = ⟨a, o⟩ := by
  show (⟨(a ++ b).take ((a ++ b).length - (n + 1)), o⟩ : Seen) = ⟨a, o⟩
  rw [List.length_append, hb, Nat.add_sub_cancel, List.take_left']
  rfl

/-- **At the fold's move number n the closing's data do not read the last n + 1 rounds shown**: "BAT"'s and the fold's
own so far. -/
theorem ask_own_free (J : CloseJob W) (n : Nat)
    (c : Handed ⟨0, 0⟩ (closeSpends J.pub.par) (closeCarries J.pub)) (a b b' : List Fmt.RoundView)
    (o : Option (List OpenedColumn)) (t : State W X) (hb : b.length = n + 1) (hb' : b'.length = n + 1) :
    closeAskAt J n c ⟨a ++ b, o⟩ t = closeAskAt J n c ⟨a ++ b', o⟩ t := by
  unfold closeAskAt
  rw [cut_own n a b o t hb, cut_own n a b' o t hb']
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closePlan
#print axioms ProofFile.Honest.K10.closePlan_iff
#print axioms ProofFile.Honest.K10.bareAsk
#print axioms ProofFile.Honest.K10.spentRun
#print axioms ProofFile.Honest.K10.askOr
#print axioms ProofFile.Honest.K10.foldShellT
#print axioms ProofFile.Honest.K10.CloseJob.over
#print axioms ProofFile.Honest.K10.lift_is
#print axioms ProofFile.Honest.K10.seat_is
#print axioms ProofFile.Honest.K10.layF
#print axioms ProofFile.Honest.K10.closeTell
#print axioms ProofFile.Honest.K10.closeSim
#print axioms ProofFile.Honest.K10.closeRounds
#print axioms ProofFile.Honest.K10.closeRounds_is
#print axioms ProofFile.Honest.K10.closeAt
#print axioms ProofFile.Honest.K10.moves_len
#print axioms ProofFile.Honest.K10.members_is
#print axioms ProofFile.Honest.K10.closeOnAt
#print axioms ProofFile.Honest.K10.closeOn
#print axioms ProofFile.Honest.K10.closeBud
#print axioms ProofFile.Honest.K10.CloseOnFree
#print axioms ProofFile.Honest.K10.askVerdict
#print axioms ProofFile.Honest.K10.CloseAskPublic
#print axioms ProofFile.Honest.K10.ExactAt
#print axioms ProofFile.Honest.K10.FreshAt
#print axioms ProofFile.Honest.K10.freshAt_of_good
#print axioms ProofFile.Honest.K10.CloseExact
#print axioms ProofFile.Honest.K10.CloseFresh
#print axioms ProofFile.Honest.K10.atN
#print axioms ProofFile.Honest.K10.phiB
#print axioms ProofFile.Honest.K10.sumB
#print axioms ProofFile.Honest.K10.runSentN
#print axioms ProofFile.Honest.K10.runSent
#print axioms ProofFile.Honest.K10.runBackN
#print axioms ProofFile.Honest.K10.runBack
#print axioms ProofFile.Honest.K10.RunOneToOne
#print axioms ProofFile.Honest.K10.runE
#print axioms ProofFile.Honest.K10.epsOf
#print axioms ProofFile.Honest.K10.CloseSentIs
#print axioms ProofFile.Honest.K10.CloseOneToOne
#print axioms ProofFile.Honest.K10.cut_own
#print axioms ProofFile.Honest.K10.ask_own_free
