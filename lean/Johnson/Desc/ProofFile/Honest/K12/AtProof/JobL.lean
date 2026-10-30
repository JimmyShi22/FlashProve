-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/JobL.lean: what a caller supplies (`TestJob`,
Johnson/Desc/ProofFile/Honest/K12/Test.lean) at the proof file's first chain's proximity test, the
sub-protocol "F:2": five of its six fields, made of part 1's own text of the part that sends the
tested message: the finish of the code switch, "F:1" (Johnson/Desc/ProofFile/Honest/K2/Half.lean,
Sending.lean, Part.lean). The sixth, the state on entry, is a parameter. Definitions with code, a
public test, and one equation.

  `finishAt`, `sentL`, `shapeL`, `freshShapeL`   the sender's place and what it announces
  `membersL`, `freshL`   the stretches that the test's parts carry; who sent the fresh table
  `asK2`, `asK2_stretchOf`   a stretch of this folder's type given its count back
  `carryRows`, `heardL`, `rowsL`, `treesL`   the rows and the tree, by the sender's own functions
  `fitsLs`, `fitsL`   a public test on the test's parameters and the sender's place
  `jobL`         the job

No second text. Every row and the column come out of part 1's `messageRows` and `sendingPar`, and
the library's `mainRows` (Johnson/Desc/K2/Honest/Carrying.lean), `Send.col`
(Johnson/Prover/Send/Core.lean) and `Own.treesMade`.

Limits.
- Five parameters are tied to nothing here: `door` (the state on entry: not shown to be the
  verifier's), `D`, `readers`, `closing` (what the fold in front of the finish leaves: the function
  that part 1's `switchLot` lays has no name of its own, so it cannot be called), and `q` against
  `p`, but for `fitsL`.
- `fitsL q p = true` is meant as a named public premise of every law on this job. Where it is false
  the text may read a random value at another place than the sender laid it; where the finish
  announces one message, `freshL` names message 0, which is a member too.
- On a refusal of the sender's text `rowsL` lays zeros (`| .error _ => zeroPS`) and `treesL` the
  message of zeros (`.toOption.getD K2.zeroMessage`), without a warning: a `TestJob`'s fields have
  no room for a refusal. WANTED BESIDE IT, BY NAME, WHEREVER `jobL` IS LAID: the closing's refusals
  hang on public fields alone. Nothing here shows it: `closing` is a parameter, and may refuse on
  the prover's input. The sender's own first move is a fault on the same refusal (K2/Part.lean,
  `switchPart`); that a run which reaches the test has not refused is shown by nothing here: till
  then "`carryRows` returns" is a named premise.
- `membersL` is not the group under test: it is all stretches on which the carrying message's rows
  hang: those that the finish carries, then its own. The docstring of `TestJob.members` says "the
  group's oracle messages": untrue of this job.
- The first stage's mask table and its tails are zeros: the carrying message has no mask row. What
  the test's text reads of them at such a stage is not treated here.
- `TestJob.first` lays the fresh table by the library's `packedN`; the sender laid it by part 5's
  `K1.Ride.lay`: that the two are one table: AtProof/FreshAtL.lean.
- Silent defaults: `heardL` yields the empty list below two challenges; `shapeL`, `freshShapeL` and
  `treesL` read arrays by `getD`; `finishAt` takes the first place without a link.
- Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.K12.Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.K2.Honest (mainRows zeroG)
open Johnson.Prover.Link (PS)
open Johnson.Prover.Send (Rows)

variable {W₀ Rc Xi Tr X : Type}

/-! ## 1 The sender's public data -/

/-- **The finish of the code switch**: the first place of that kind which has no link, with its
public data as part 1's `switchPlaces` makes them. None where there is no such place. That there is
just one is not shown here. -/
def finishAt (Z : Pub) (G : Ground) : Option K2.SwitchPlace :=
  (K2.switchPlaces Z G).find? fun p => p.place.link.isNone

/-- The messages that the finish announces. -/
def sentL (p : K2.SwitchPlace) : Array OnBytes.OracleNotice := K2.switchSent p.sizes p.others

/-- The carrying message's shape: message 0. -/
def shapeL (p : K2.SwitchPlace) : OnBytes.OracleShape := ((sentL p).getD 0 default).shape

/-- **The stretches that the test's parts carry**: those that the finish itself carries, in its own
order, then the carrying message's own. -/
def membersL (p : K2.SwitchPlace) : List (Addr × ℕ × Due) :=
  p.front ++ [(⟨p.place, 0⟩, 0, K2.messageDue p.sizes.codes (shapeL p) none)]

/-- The first fold's fresh table is the last message that the finish announces. -/
def freshL (p : K2.SwitchPlace) : Option (Addr × ℕ) := some (⟨p.place, 0⟩, (sentL p).size - 1)

/-! ## 2 The rows and the tree, by the sender's own text -/

/-- **A stretch by number, as part 1's text takes it: with its count.** This folder's `Stretch`
(Coins.lean) has lost the count and yields 0 beyond it; part 1's (`K2.Stretch`, K2/Part.lean) bears
it and refuses beyond it. d: the count, public. -/
def asK2 (d : Due) (s : Stretch) : K2.Stretch := ⟨d, ⟨fun i => s.f i, fun i => s.e i⟩⟩

/-- It undoes `stretchOf`. -/
theorem asK2_stretchOf {d : Due} (c : Cs d) : asK2 d (stretchOf c) = K2.Stretch.of c := by
  obtain ⟨f, e⟩ := c
  simp [asK2, stretchOf, K2.Stretch.of]

/-- **The carrying message's rows in full**: part 1's `messageRows` at the message's own stretch,
its data the library's `mainRows` at what `closing` returns of the stretches that the finish
carries. heard: the challenges in front of the finish. A refusal is handed on. -/
def carryRows (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) (mem : ℕ → Stretch) :
    Except String Rows :=
  (closing p (D w.x) (readers w) heard fun n =>
      match p.front[n]? with
      | some x => .ok (asK2 x.2.2 (mem n))
      | none => .error "a stretch is asked beyond the list").bind fun Wl =>
    K2.messageRows K2.freshTable p.sizes.codes (shapeL p) none
      (mainRows p.sizes Wl (fun _ _ _ => zeroG) 0)
      (asK2 (K2.messageDue p.sizes.codes (shapeL p) none) (mem p.front.length))

/-- The challenges in front of the finish, of those in front of the test: all but the last two.
Meant for a chain in which the test stands right behind the finish, whose half is one part of two
rounds (K2/Half.lean): nothing here holds that of a chain but `fitsL`'s clause on the places. -/
def heardL (fr : Front X) : List Fmt.Drawn := fr.heard.take (fr.heard.length - 2)

/-- A state of zeros. -/
def zeroPS : PS :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
    fun _ => 0⟩

/-- **The first stage's rows.** The main table by index: the row's number in the low bits. No mask
row: the carrying message has none. WHERE THE SENDER's TEXT REFUSES: ZEROS, WITHOUT A WARNING. -/
def rowsL (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (fr : Front X) (mem : ℕ → Stretch) : PS :=
  match carryRows D readers closing p w (heardL fr) mem with
  | .ok R =>
    { zeroPS with
      tabM := fun i => R.mainE (i % 2 ^ OnBytes.ceilLog2 (shapeL p).mainRows)
        (i / 2 ^ OnBytes.ceilLog2 (shapeL p).mainRows)
      tM := R.mainTlE }
  | .error _ => zeroPS

/-- **The one tree that the first round of positions opens**: the library's written column
(`Johnson.Prover.Send.col`) over the finish's messages: message 0's rows as above; the last
message's mask row and its tail out of the first stage's state. Its depth: the library's
`Own.treesMade`. Where the sender's text refuses: message 0 is `K2.zeroMessage`. -/
def treesL (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (p : K2.SwitchPlace) (w : Local W₀ Rc Xi Tr) (fr : Front X) (mem : ℕ → Stretch) (P : PS) :
    List Tree :=
  let R₀ := (carryRows D readers closing p w (heardL fr) mem).toOption.getD K2.zeroMessage
  let V : ℕ → Rows := fun k =>
    if k == 0 then R₀
    else if k == (sentL p).size - 1 then { K2.zeroMessage with mask := P.fM, maskTl := P.fT }
    else K2.zeroMessage
  let lay := (VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}
  [((lay.shapes.getD 0 default).logN,
    Johnson.Prover.Send.col (K2.sendingPar p.sizes.codes (sentL p)) V 0)]

/-! ## 3 A public test on the two places -/

/-- The fresh message's shape: the last that the finish announces. -/
def freshShapeL (p : K2.SwitchPlace) : OnBytes.OracleShape :=
  ((sentL p).getD ((sentL p).size - 1) default).shape

/-- **The clauses of the test, each with its name.** q: the test's parameters. p: the sender's
place. They are public numbers alone. The first bars that one stretch is member and fresh table at
once; the others decide at which place of the test's first state a random value of the sender's is
read, where the test stands, and which tree it opens; three are the public tests on which the
sender's own `messageRows` refuses (part 5's `K1.rideFits`, which holds 2 k - h + 1 ≤ the mask
code's message length; `Own.sentShapeFits`; the count). -/
def fitsLs (q : P12) (p : K2.SwitchPlace) : List (String × Bool) :=
  let s := q.nums.stages.headD default
  let c := p.sizes.codes.base.getD (shapeL p).code default
  let z := p.sizes.codes.mask.getD (freshShapeL p).maskCode default
  let lay := (VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}
  [("two messages", (sentL p).size == 2),
   ("the fresh table came earlier", !q.nums.ownMask),
   ("h ≤ k", decide (s.h ≤ s.k)),
   ("main rows", 2 ^ s.k == (shapeL p).mainRows && (shapeL p).maskRows == 0 &&
      (shapeL p).mainDeg == 3),
   ("fold rounds", s.k == p.foldVars),
   ("mask rows", 2 ^ s.h == (freshShapeL p).maskRows && (freshShapeL p).mainRows == 0),
   ("the main code", s.C.l == c.ell && s.C.r == c.r),
   ("the mask code", s.Z.l == z.ell && s.Z.r == z.r),
   ("the fresh table fits its message", K1.rideFits p.sizes.codes (freshShapeL p) ⟨s.k, s.h⟩),
   ("the carrying message's shape fits",
      VerifiableInference.Desc.Own.sentShapeFits p.sizes.codes (shapeL p)),
   ("the carrying message's count", K2.messageDue p.sizes.codes (shapeL p) none ==
      ⟨0, (shapeL p).mainRows * c.r +
        ((VerifiableInference.Desc.Own.padMade p.sizes.codes (shapeL p)).getD []).length⟩),
   ("two stages or more", decide (2 ≤ q.nums.stages.length)),
   ("the fresh table's count",
      K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) == ⟨0, dueFresh s⟩),
   ("right behind", q.place == ⟨p.place.chain, none, p.place.piece + 1, .K12⟩ &&
      p.place.link.isNone),
   ("one tree", q.nums.first.map (fun x => (x.1.a, x.1.W)) ==
      lay.shapes.toList.map fun t => (t.logN, t.mainWidth + t.maskWidth)),
   ("one tree alone", lay.shapes.size == 1)]

/-- **The test.** -/
def fitsL (q : P12) (p : K2.SwitchPlace) : Bool := (fitsLs q p).all (·.2)

/-! ## 4 The job -/

/-- **The job at the first chain's proximity test.** q: the test's parameters. door: the state on
entry, a parameter. -/
def jobL (q : P12) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    TestJob (Local W₀ Rc Xi Tr) X :=
  { p := q, members := membersL p, fresh := freshL p, rec₀ := door
    rows₀ := rowsL D readers closing p, trees₀ := treesL D readers closing p }

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.finishAt
#print axioms ProofFile.Honest.K12.AtProof.sentL
#print axioms ProofFile.Honest.K12.AtProof.shapeL
#print axioms ProofFile.Honest.K12.AtProof.membersL
#print axioms ProofFile.Honest.K12.AtProof.freshL
#print axioms ProofFile.Honest.K12.AtProof.asK2
#print axioms ProofFile.Honest.K12.AtProof.asK2_stretchOf
#print axioms ProofFile.Honest.K12.AtProof.carryRows
#print axioms ProofFile.Honest.K12.AtProof.heardL
#print axioms ProofFile.Honest.K12.AtProof.zeroPS
#print axioms ProofFile.Honest.K12.AtProof.rowsL
#print axioms ProofFile.Honest.K12.AtProof.treesL
#print axioms ProofFile.Honest.K12.AtProof.freshShapeL
#print axioms ProofFile.Honest.K12.AtProof.fitsLs
#print axioms ProofFile.Honest.K12.AtProof.fitsL
#print axioms ProofFile.Honest.K12.AtProof.jobL
