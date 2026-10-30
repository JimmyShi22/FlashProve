-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Text.lean: kind K13, THE MEMBERS' BATCHING AND THE LINEAR CLAIM's FIRST PART: the
functions that decide. Definitions with code; no theorem. Plain functions on data. EACH TEST REFUSES
UNDER A NAME OF ITS OWN.

WHAT THE KIND IS FOR. Each link of a proof file's first chain leaves rows on the committed matrix of
weights: claims < g (x) eq(psi, .), M > + < mask form > = target. Behind the last link they lie on a
pile. K13 makes ONE row of them, by random weights and a sumcheck over the matrix's column
variables, reads that row as the claim of the test on the table, and, when the witness W of that
test has been committed to, lays the request's own group of oracle messages with the row (Eval).

ROUNDS (of the batching; the other parts have none). "BAT-sigma": the prover sends nothing; one
element x is drawn; the plan's entry counts the rows of the pile. "PSC epsilon": the prover sends
the sum of a hiding polynomial; one element is drawn. Then one round "PSC round" for each of the
kCol column variables: two coefficients of the round's polynomial of degree 2 are sent (the linear
one is left out: the round's equation fixes it); one element is drawn.
READS. Nothing.
DECIDES. front: where a reply is due on the chain (a proof file's first chain: yes; a key file's:
no), one has been heard; the pile has as many rows as the plan counts; the rows and the message of
index masks have the form that the table's shape asks. batt: nothing is owed from the round closed
before; the pile's rows are counted; row j gets the weight x^j; 1 + 2 kCol fresh mask entries are
taken for the hiding polynomial; the sumcheck's rounds are read and its last claim is
written as one row at the point drawn. NO TEST ON A VALUE STANDS HERE: a false row on the pile makes
the one row false, but for the draws' errors. quiet: the table's shape is lawful under the codes;
what W's message holds. rows: the own group; the messages of the claim's masks, W and, where the
shape asks it, the split's message join it; the row (Eval) is laid.
NOT HERE: that the reply which was heard is the reply that the caller asks about: the asked reply
never comes into these functions: the file's last test compares.

WHAT IS NOT ASKED HERE, BECAUSE IT IS ASKED ONCE, IN FRONT: what a round holds and draws (how many
items of which sort; how many elements, positions, matrix entries): the rounds are data of the
kind's blocks (Johnson/Desc/K13/Kind.lean), and the format's step holds each round against them
before it decides. The readings here (oneRound, heard) unwrap what that test has passed; each still
refuses under a name.

Typed after `verify-on-bytes`'s firstBlock (OnBytes/Proof/File.lean), memberFirstVerify,
linFirstVerify and linFirstRows (OnBytes/Iop/Lin.lean), Batt.verify (OnBytes/Iop/Batt.lean),
Psc.hear and Psc.verify (OnBytes/Iop/Psc.lean). Its plain records (TensorRow, LinShape, LinClaim,
LinFirst, Psc.Heard) are used as data. Its PURE functions that are called by name: memberClaim,
Batt.masksOf, Batt.claimOf, Batt.summandOf, Batt.rowOf, E.ofTriple, linLayW, listOfT. FIVE
THAT CAN REFUSE ARE THE KIND'S OWN TEXT (Johnson/Desc/K13/Own.lean: pileOnTable, pileForm, runSum,
messageW, evalRow, for memberRowsFit, Batt.fits, Psc.run, linMessageW, linEvalRow; with them
splitNeeded for LinShape.ownSplitNeeded; that they agree at all arguments:
Johnson/Desc/K13/OwnLaws.lean); each is asked here under the name that its test bears. A SIXTH, the
test on the public shape, is the description's own text too (Johnson/Desc/Own/Lin.lean: linFits, for
linOk; that they agree: Johnson/Desc/Own/LinAgree.lean: linFits_eq). The reading
of a round's items is sentE
(Johnson/Desc/K13/PscStep.lean). The effects on the statement are the ground's plain functions
takeMasksP, newGroupP, joinP and addRowsP (Johnson/Desc/First/Base/Ground.lean), by name.

What is not claimed. That a function here is the program's routine: no theorem says so. That a word
of a sent or drawn element is below the field's prime: that test belongs to the fold that calls
these functions. Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Lin
import Johnson.Desc.First.Fork.Ground
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.K13.PscStep
import Johnson.Desc.K13.Own
import Johnson.Desc.Own.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes OnBytes.Params
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.Ground (takeMasksP newGroupP joinP addRowsP)
open VerifiableInference.Desc.First.End (sentE)

/-- An answer, or the name of the test that refused. -/
abbrev Ans (α : Type) : Type := Except String α

/-- A test, under its name. -/
def need (name : String) (b : Bool) : Ans Unit := if b then .ok () else .error name

/-- A value that must be there, under the name of the test that it is. -/
def there {α : Type} (name : String) : Option α → Ans α
  | some x => .ok x
  | none => .error name

/-- The statement with the book of trees, as the ground's functions take it. -/
abbrev St : Type := _root_.Desc.Plain.DState Unit

/-! ## The front -/

/-- **The front.** due: a reply is due on this chain. heard: the reply as a link has taken it off
the channel. n: the rows that the plan counts. -/
def front (st : Statement) (S : LinShape) (indexMasks : Nat) (pile : List TensorRow)
    (due : Bool) (heard : Option E) (n : Nat) : Ans Unit := do
  need "K13.reply-heard" (!due || heard.isSome)
  need "K13.pile-count" (pile.length == n)
  need "K13.pile-on-the-table" (Own.pileOnTable st S indexMasks pile).isOk

/-! ## The batching -/

/-- The one element that a round has drawn. -/
def oneDrawn (name : String) (r : Fmt.RoundView) : Ans E :=
  there name (match r.drawn.elems with | [x] => some (E.ofTriple x) | _ => none)

/-- A round in which elements are sent and one is drawn: what was sent, what was drawn. -/
def oneRound (r : Fmt.RoundView) : Ans (List E × E) := do
  let q ← there "K13.read-elements" (sentE r)
  let x ← oneDrawn "K13.read-one-drawn" r
  pure (q, x)

/-- What is heard in the sumcheck's rounds. It takes the first item of the first round, and of each
further round whatever items it holds: how many there are is asked in front, with the rounds. -/
def heard : List Fmt.RoundView → Ans Psc.Heard
  | [] => .error "K13.read-first-round"
  | r₀ :: l => do
    let a ← oneRound r₀
    let mu ← there "K13.read-sum" a.1.head?
    let inX ← l.mapM oneRound
    pure ⟨mu, a.2, inX, []⟩

/-- **The batching.** owed: the rows that are still owed a count. n: the rows that the entry of
"BAT-sigma" counts. ledger: the message whose mask rows give the fresh entries. rs: the 2 + kCol
rounds. Returns the one row. -/
def batt (owed : RowsOwed) (kCol n : Nat) (pile : List TensorRow) (ledger : Nat) (d : St)
    (rs : List Fmt.RoundView) : Ans (TensorRow × St) := do
  need "K13.nothing-owed" owed.isNone
  need "K13.pile-form" (Own.pileForm kCol pile).isOk
  match rs with
  | [] => .error "K13.sigma-round"
  | r :: rs' =>
    let x ← oneDrawn "K13.sigma-one-drawn" r
    need "K13.rows-counted" (pile.length == n)
    let t ← there "K13.mask-entries" (takeMasksP d ledger (Batt.masksOf kCol))
    let h ← heard rs'
    let o ← there "K13.sumcheck-sizes"
      (Own.runSum (Batt.claimOf pile x) (Batt.summandOf pile x) (t.1.map fun i => ⟨ledger, i⟩)
        h).toOption
    need "K13.a-coefficient-a-row" (o.rowMaps.length == pile.length)
    pure (Batt.rowOf pile o, t.2)

/-! ## In front of W's commitment, and behind it -/

/-- In front of W's commitment: what the prover's message holds. -/
def quiet (codes : Codes) (S : LinShape) : Ans (Array OracleNotice) := do
  need "K13.shape-lawful" (VerifiableInference.Desc.Own.linFits codes S)
  there "K13.message-W" (Own.messageW S).toOption

/-- Messages join a group, one behind the other. -/
def joinAll (g : Nat) : List Nat → St → Ans St
  | [], d => pure d
  | o :: l, d => do
    let d' ← there "K13.join-masks" (joinP d g o false)
    joinAll g l d'

/-- **Behind W's commitment**: the request's own group, the joinings, the row (Eval). ids: the
numbers of the messages sent. -/
def rows (S : LinShape) (claim : LinClaim) (ids : Array Nat) (d : St) : Ans (LinFirst × St) := do
  let w ← there "K13.W-sent" ids[0]?
  let b ← there "K13.own-group" (newGroupP d S.w.code S.ownMaskCode)
  let d₁ ← joinAll b.1 (listOfT (claim.masks.toList.map (·.oracle))) b.2
  let d₂ ← there "K13.join-W" (joinP d₁ b.1 w false)
  let split ← there "K13.split-sent" (if Own.splitNeeded S then ids[1]? else some noId)
  let d₃ ← there "K13.join-split"
    (if Own.splitNeeded S then joinP d₂ b.1 split false else some d₂)
  let mask ← there "K13.mask-sent" (if S.masksAhead then ids.back?.map some else some none)
  let row ← there "K13.eval-row" (Own.evalRow S claim w (linLayW d₃.st.codes S)).toOption
  let d₄ ← there "K13.eval-laid" (addRowsP d₃ b.1 [row])
  pure ({ w := w, split := split, own := b.1, mask := mask, claim := claim }, d₄)

end VerifiableInference.Desc.K13
