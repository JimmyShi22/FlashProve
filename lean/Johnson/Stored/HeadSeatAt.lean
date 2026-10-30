-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/HeadSeatAt.lean.
WHAT IT IS. The seat of the output head's own rounds (Desc/Kinds/HeadFrame.lean: Seat) at the first
chain's carried record (Desc/First/State.lean: S), and the kind's block there. A description that
seats seatedOf, or Stored/HeadAddsAtS.lean's seatedClaims, RUNS THIS TEXT at the head's own rounds:
what a field of the seat reads or lays is then part of what the verifier decides.
WHAT IT DOES NOT SHOW. Definitions alone. That the seat gives back what is laid, that the block
leaves the rest of the record, and what its yes means: the files under Desc/Kinds/Law/.
WHAT THE SEAT READS. The next token: out.reply. The ledger: S.fork?. The lookup's points:
S.lookHeard?: nothing until the lookup is heard. The request's public part: S.tokv, S.rowR, S.rowE:
functions of the request file's words, which the record's start lays (S.req); where no words are
laid the request has no token and r = e = 0. A TOKEN FOR WHICH NO WORD IS LAID READS AS 0: so the
kind's part of the test on the instance (Par.okStart) would say yes at a request that is too short.
THE SEATED BLOCK's DECISION THEREFORE ASKS THE RECORD's OWN TEST ON THE REQUEST (S.reqOk: T + 2
words; every token an entry of the vocabulary; r < e <= T) AT THE KIND's OWN NUMBERS (startOk); the
kind's own block (blockOf) asks neither. The twelve reads: off the table of tables that the reads'
quiet step has laid (t) and the reads' array in the ledger: REFUSED unless the array is there with a
column and each of the twelve tables is found and long enough (readsNeed). The three further reads
for the lookup's run "planes" (planesAt): refused unless the array is there with a column.
WHAT THE SEAT LAYS. The ledger: S.putFork?, which refuses where the record has no ledger's part.
What was heard: x := heardOf (HeadSeat.lean) at the lookup's value in lookHeard: REFUSED UNDER A
NAME where the record does not stand in the head's link or the lookup is not heard. In front of this
block x is none: it has this one writer. The state of the squares' level's sumcheck: squaresP.
WHAT WAS HEARD, FOR THE CLAIMS: read back out of x, the ledger and squaresP (allOf, HeadSeat.lean).
WHAT HAS NO SEAT IN S: the claim on the weights and the key vectors: the two layings leave S as
it is.

-/
import Johnson.Desc.First.State
import Johnson.Desc.Kinds.HeadBlock
import Johnson.Desc.Kinds.HeadCaller
import Johnson.Desc.First.Look.K3Seat
import Johnson.Stored.HeadSeat
import Johnson.Stored.ReplySeatAt
import Johnson.Desc.Kinds.HeadLaid
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The sizes, of the head's public numbers. -/
@[reducible] def sizesOf (h : Model.Head.Shape) : Sizes :=
  { lt := h.lt, ls := h.ls, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
    sh := h.digSh, F := h.famF }

/-- The request's public part, off the record: the tokens; the first checked position; one behind
the last: of the request file's words, which the record's start lays (State.lean: req). -/
@[reducible] def requestOf (s : S) : Request :=
  { tok := fun i => s.tokv.getD i 0, r := s.rowR, e := s.rowE }

/-- The place's parameters. work: the setting's bits of work in front of a challenge whose error is
a field's, in a request's own rounds. BEFORE IS LAID EMPTY HERE: under which numbers the messages
with the head's and the stream's cells are sent is the lot's to say: THE BLOCK THAT A LOT SEATS IS
seatedOf, further down, which lays that list and tests the laid numbers. -/
def parOf (h : Model.Head.Shape) (work : Nat) : Par :=
  { sizes := sizesOf h, policy := { C := h.clipC, theta := h.theta, cap := h.cap }, sT := h.tabS,
    floor := Model.Head.keyFloor h, work, before := [] }

/-- The twelve tables of reads that the text's forms name, by the program's names, each with the
number of entries that the text spends of it (the laws' readLen | readLenN, written again). -/
def readsNeed (h : Model.Head.Shape) : List (String × Nat) :=
  let _ := sizesOf h
  let stream := 5 * Norm.d / Norm.S2
  let wide := (4 * Norm.d + 6 * JV) / Norm.S2
  [("xbL@Z_V", stream), ("xbL@Y_N", stream), ("hd@zt_FC", 2 * Norm.d), ("hr@zt_ROW", NR + 21),
   ("hr@P_V", NR), ("hr@r_tV", NR), ("hr@rt_N", NR), ("hf@Z", wide), ("hf@phiZ", wide),
   ("hd@r_H", 2 * Norm.d), ("hr@phiC", NR + 21), ("hr@rhoC", NR + 21)]

/-- **The seat at S.** iU3: the number of the reads' array. THE READER OF A READ REFUSES: there are
no reads unless the array is there with a column, and each of the twelve tables is there and is no
shorter than what the text spends of it. -/
def seatAt (h : Model.Head.Shape) (iU3 : Nat) : Seat S where
  toSeat := Reply.seatAt
  request s := requestOf s
  ledger s := s.fork?.getD {}
  lookup s := s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])
  reads s := match s.here, s.fork? with
    | .head o, some F => o.t.bind fun tt => (F.trees[iU3]?).bind fun tr =>
      let cols := tr.K
      if cols == 0 || !((readsNeed h).all fun n =>
          (tt.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) then none
      else some <|
      let at_ (name : String) (i : Nat) : Form :=
        let pos := ((tt.tab.find? fun e => e.1 == name).map (·.2.1)).getD 0 + i
        Aff.ent iU3 (pos / cols) (pos % cols)
      show _ from
        ({ entry := fun x => at_ (match x with
            | .streamAtSquares => "xbL@Z_V" | .streamAtNormed => "xbL@Y_N"
            | .actAtKeys => "hd@zt_FC" | .rowAtKeys => "hr@zt_ROW" | .rowAtPV => "hr@P_V"
            | .rowAtProducts => "hr@r_tV" | .rowAtNormed => "hr@rt_N")
           wide := at_ "hf@Z" },
         { entry := fun x => at_ (match x with
            | .wideAtKeys => "hf@Z" | .wideAtCosts => "hf@phiZ" | .actAtLogits => "hd@r_H"
            | .rowAtCosts => "hr@phiC" | .rowCount => "hr@rhoC") })
    | _, _ => none
  heard s := match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none
  setLedger s F := s.putFork? F
  setHeard s H := match s.here with
    | .head o =>
      match o.lookHeard with
      | some g =>
        let _ := sizesOf h; let _ := requestOf s
        let _ : Token := ⟨(s.out.reply.map OnBytes.Desc.Reply.tokOf).getD 0⟩
        .ok { s with here := .head { o with
          x := some (heardOf g H), squaresP := some (pscOf H.1.squares.psc false) } }
      | none => .error "the head's seat: what the lookup left is not laid"
    | _ => .error "the head's seat: the record does not stand in the head's link"
  setWeightClaim s _ := s
  setKeyForms s _ := s

/-- The three further reads at S (HeadSeat.lean: planeEntry). For the lookup's run "planes":
readers := callerReaders (planesAt iU3). IT REFUSES AS reads DOES: nothing unless the reads' array
is there with a column. (A table that is not found, and an entry at or beyond a table's length, are
refused by planeEntry itself.) -/
def planesAt (iU3 : Nat) : PlaneSeat S := fun s =>
  match s.here, s.fork? with
  | .head o, some F =>
    o.t.bind fun tt => (F.trees[iU3]?).bind fun tr =>
      if tr.K == 0 then none else some (planeEntry tt.tab iU3 tr.K)
  | _, _ => none

/-- **The kind's block at S**, at piece 4 of link number l of the first chain. A claim is a letter
here: the unit type. -/
def blockAt (h : Model.Head.Shape) (iU3 work l : Nat) : Block S Unit :=
  kindWithJoin (K3.seatCalls fun _ => ()) (seatAt h iU3) l 4 (parOf h work)

/-- The same, of the public record that the program makes of the public files; nothing if its plan
names no array of reads. -/
def blockOf (W : Model.Verify.Public) (l : Nat) : Option (Block S Unit) :=
  (W.H.tl.ix.U.getD 2 none).map fun iU3 =>
    blockAt W.hS iU3 ((Params.settingOf W.P.frame).workOf .field .request) l

/-! ## The block as a lot seats it

WHY THERE ARE TWO NAMES. blockOf is the kind's block at this record, general: its tests on the plan
are the kind's own (Par.ok), and it names no message. Three things are THE SEAT's, because only the
seat holds the numbers and the record: how the arrays are laid (the border of the stream's array;
HeadLaid.lean's tests), the record's own test on the request (startOk), and under which numbers of
sending the head's and the stream's cells go out ("before"). seatedOf lays these over blockOf's
block and turns nothing else: Law/SeatedBridge.lean has name, place, rounds, oracles and runs equal
by rfl, and the decision equal wherever the test on the request says yes. THE SEATED CONSTANT IS
seatedOf (at true claims: HeadAddsAtS.lean's seatedClaims): a lot that seats blockOf itself seats a
block with an idle "before" and without the tests on the laid numbers and on the request. -/

/-- The numbers beside the sizes (HeadLaid.lean), of the head's public numbers and the border of the
stream's array. -/
def laidAt (h : Model.Head.Shape) (b : Model.Head.Border) : Laid :=
  { la := h.la, padLog := h.lPd, limbs := h.XL, laidLimbs := b.nl, off := b.off,
    step := b.cnt * b.J, room := b.kxb * (b.mxb / 2 ^ h.la) }

/-- HeadLaid.lean's named tests, at the public record. -/
def laidOk (W : Model.Verify.Public) : Bool :=
  let _ := (parOf W.hS 0).sizes
  let _ := (parOf W.hS 0).policy
  (laidAt W.hS (Model.Verify.borderOf W.y)).ok

/-- The record's own test on the request (State.lean: S.reqOk), at the kind's own numbers: T = 2^lt
positions and the head's vocabulary: there are T + 2 words, every token is an entry of the
vocabulary, r < e <= T. -/
def startOk (W : Model.Verify.Public) (s : S) : Bool := s.reqOk (2 ^ W.hS.lt) W.hS.V

/-- A block with one test more on the plan, one test on the record in front of its decision, and the
list of the oracle messages that must have been sent in front of its first draw. ALL ELSE IS THE
BLOCK's: its name, place, rounds, oracles, runs; and its decision wherever the test on the record
says yes. -/
def tested {Cl : Type} (ok : Bool) (start : S → Bool) (before : List (Nat × Nat))
    (b : Block S Cl) : Block S Cl :=
  { b with
    planOk := b.planOk && ok
    before := before
    decide := fun s rs gs =>
      if start s then b.decide s rs gs else .error "the request: rows and tokens" }

/-- **K6's BLOCK AS A LOT SEATS IT**: blockOf's, with HeadLaid.lean's tests on the plan, with the
record's own test on the request in front of its decision, and with before: the oracle messages with
the head's cells and with the stream's, each by its chain and its number of sending: THE LOT's TO
SAY, WITHOUT A DEFAULT: they are numbers of the plan's declared rounds, which this file does not
read. -/
def seatedOf (W : Model.Verify.Public) (l : Nat) (before : List (Nat × Nat)) :
    Option (Block S Unit) :=
  (blockOf W l).map (tested (laidOk W) (startOk W) before)

end VerifiableInference.Desc.Kinds.Head
