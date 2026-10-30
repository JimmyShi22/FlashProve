-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Part.lean: the honest side of the kind "the code switch" (K2;
Johnson/Top/H0/Tw/K2C/Kind.lean), in the form of Honest/Frame.lean: THE PART. It defines part of the
honest prover. Definitions with code; no theorem.

The rounds. Two at every place of the kind, and they are one part: "SEND seed", whose message holds
the roots of the trees over the switch's oracle messages; "LOC", whose message holds the answers to
their out-of-domain samples. Behind "LOC" the trees of the group that was closed are read at the
drawn positions: these tables were sent in front of this part, so it sends nothing for that.

What is this kind's own, and what is called. What stands in the main rows of the messages is
Johnson/Desc/K2/Honest/Carrying.lean's. To lay tails, pads and mask rows out of the part's coins, to
encode the rows, to lay the symbols into the trees' tables and to answer the samples is the work of
A SENDING, which many kinds share. It is A LETTER here, `Sender`: two functions with code. So this
file types no encoding and no answer.

  `Stretch`, `Stretch.of`, `Stretch.cut`, `Stretch.fs`, `Stretch.es`, `Stretch.carried`   coins with
                  their count, read by number
  `messageDue`, `foldAt`, `dueBefore`, `sendingDue`   how many coins one oracle message takes; a
                  sending
  `Sender`       the shared sending, as this kind calls it
  `SwitchAsk`    what the part reads of the prover's input: a small structure
  `switchSent`, `switchFresh`   the messages that a switch announces; which is the fresh mask
  `switchRowsAt`   the main rows of these messages in a run
  `Sizes.restLength`, `Sizes.asStatement`, `Sizes.asRows`, `Sizes.roomy`   a public test: the sizes
                  fit a switch: the verifier's own test on the target, called
  `switchPart`   the part

Coins. The part takes the coins of all its new messages and spends none of another part's. By
message, in the order of sending; in a message: the main rows' tails, row 0 first; the pad, if it
lies in a main row, answer 0 first (three coins an answer over the base field); all entries of the
mask rows, entry c of row ρ of m rows at c * m + ρ; the mask rows' tails, row 0 first. The coins of
each field are numbered through all messages. A carrying message has no mask row, and the room that
it leaves free holds zeros: it takes its two rows' tails and its pad. A kept member's copy takes new
tails and a new pad.
A FOLD's FRESH MASK is no row of free entries: its table is made of the 2 k + 1 coefficients of the
fold's hiding polynomial, k the fold's row variables, and holds 0 beyond them
(docs/format/toys/1-product.md, part 3: a page outside this library). It takes these coefficients,
then its rows' tails. THE COEFFICIENTS' ORDER: by variable, in the order of the fold's rounds; in a
variable by rising degree; the constant counts as the last variable's degree 0: a_1, b_1, ..,
a_(k-1), b_(k-1), w, a_k, b_k, where a_l goes with X_l and b_l with X_l ^ 2. That page's example
lists them in this order.
THE PART OWNS THE NEXT SEGMENT's MASK ROW AND THE NEXT FOLD's FRESH MASK: later parts spend entries
of the first and the coefficients of the second.
It CARRIES one stretch for each oracle message on whose coins the closed group's rows hang: their
names and counts are an argument, public data.
NO VALUE STANDS IN FOR A COIN: a read beyond a stretch's count, or of a stretch beyond the list, is
a refusal, and so a fault of the move that reads.

Stops. None of either sort. The one test on a drawn value in the kind's text asks that no seed's
factor is 0 (Johnson/Desc/Ground/Calls.lean, `sendP`). A list of challenges at which a factor is 0
is none that the round can draw: `drawFit` (Honest/Frame.lean) asks `drawsMarkedNonzeroHaveNonzeroWords`, as `roundsFit`
(Johnson/Desc/Block.lean) does in front of every decision.

Limits. `messageDue` counts no masking word of a proximity test's last step: a switch between
segments sends none. Nothing holds a `Sender` against the description's text. The part has no
simulator here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.K2.Honest.Carrying
import Johnson.Top.H0.Tw.K2.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Left Sizes mainRows rest zeroG)

/-! ## 1 Coins with their count -/

/-- Coins of the two fields, with their count. -/
structure Stretch where
  due : Due
  coins : Cs due

/-- Coins as a stretch. -/
def Stretch.of {d : Due} (c : Cs d) : Stretch := ⟨d, c⟩

/-- The n coins from the numbers a on. A refusal where they are not all there. -/
def Stretch.cut (s : Stretch) (a n : Due) : Except String Stretch :=
  match s.coins.cut a n with
  | some c => .ok ⟨n, c⟩
  | none => .error "coins are asked beyond the count"

/-- The n coins of the base field from number a on. A refusal beyond the count. -/
def Stretch.fs (s : Stretch) (a n : Nat) : Except String (Array Cb.Gl.F) :=
  ((List.range n).mapM fun i => s.coins.fAt (a + i)).map List.toArray

/-- The like of the extension field. -/
def Stretch.es (s : Stretch) (a n : Nat) : Except String (Array Cb.Gl.E) :=
  ((List.range n).mapM fun i => s.coins.eAt (a + i)).map List.toArray

/-- The stretch number n, from 0, of coins for a list of named counts. A refusal beyond the list. -/
def Stretch.carried : (ds : List (String × Due)) → CsAll ds → Nat → Except String Stretch
  | [], _, _ => .error "a stretch is asked beyond the list"
  | d :: ds, c, 0 =>
    let c' : Cs d.2 × CsAll ds := c
    .ok (Stretch.of c'.1)
  | d :: ds, c, n + 1 =>
    let c' : Cs d.2 × CsAll ds := c
    Stretch.carried ds c'.2 n

/-! ## 2 How many coins a sending takes -/

/-- **The coins of one oracle message.** fold: `some k` where the message is the fresh mask of a
fold with k row variables. -/
def messageDue (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (fold : Option Nat) : Due :=
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  match fold with
  | some k => ⟨0, 2 * k + 1 + s.maskRows * z.r⟩
  | none =>
    let pad := if s.maskRows != 0 then 0 else s.answers
    let mask := s.maskRows * (z.ell + z.r)
    if s.mainDeg == 3 then ⟨0, s.mainRows * c.r + pad + mask⟩
    else ⟨s.mainRows * c.r + 3 * pad, mask⟩

/-- Whether the message number n of a sending is a fold's fresh mask, and of how many row variables.
fresh: the number of the one message that is, with the fold's row variables. -/
def foldAt (fresh : Option (Nat × Nat)) (n : Nat) : Option Nat :=
  fresh.bind fun x => if x.1 == n then some x.2 else none

/-- The coins of the first n messages of a sending. -/
def dueBefore (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n : Nat) : Due :=
  (sent.toList.take n).zipIdx.foldl
    (fun d x => d.plus (messageDue codes x.1.shape (foldAt fresh x.2))) ⟨0, 0⟩

/-- **The coins of a sending.** -/
def sendingDue (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) : Due :=
  dueBefore codes sent fresh sent.size

/-! ## 3 The shared sending, as a letter -/

/-- **A sending with its out-of-domain answers**, as this kind calls it: two functions with code.
Both are handed the codes; the messages announced; which of them is a fold's fresh mask; what stands
in their main rows outside the pads (message, row, place); the sending's coins. A refusal is a
fault. -/
structure Sender where
  /-- for each tree over the messages, in the order of the roots: the table beneath the root -/
  tables : (codes : OnBytes.Codes) → (sent : Array OnBytes.OracleNotice) →
    (fresh : Option (Nat × Nat)) → (Nat → Nat → Nat → Cb.Gl.E) →
    Cs (sendingDue codes sent fresh) → Except String (List Table)
  /-- the answers, by sampled message and then by number: of the elements that the round of seeds
  has drawn, too -/
  answers : (codes : OnBytes.Codes) → (sent : Array OnBytes.OracleNotice) →
    (fresh : Option (Nat × Nat)) → (Nat → Nat → Nat → Cb.Gl.E) →
    Cs (sendingDue codes sent fresh) → List Fmt.Ext3 → Except String (List Cb.Gl.E)

/-! ## 4 The part -/

/-- **What the part reads of the prover's input.** -/
structure SwitchAsk where
  /-- what the fold that closed the group in front leaves: of THE CHALLENGES IN FRONT OF THE PART,
  and of the stretches that the part carries, by their number in its list -/
  left : List Fmt.Drawn → (Nat → Except String Stretch) → Except String Left
  /-- the next segment's own messages of moment 0: message, row, place -/
  own : Nat → Nat → Nat → Cb.Gl.E

/-- The messages that a switch announces, in the order of sending. others: the next segment's own
messages of moment 0, then the next fold's fresh mask. -/
def switchSent (Z : Sizes) (others : Array OnBytes.OracleNotice) : Array OnBytes.OracleNotice :=
  Tw.K2.switchNotices Z.target others

/-- The fresh mask is the last message that a switch announces. k: the next fold's row variables. A
SECOND DECLARATION HAS THIS SHORT NAME: the theorem `ProofFile.Honest.K2.Law.switchFresh`
(Honest/K2/Law/FreshAtProof.lean), which proves the
statement `SwitchFresh`: it is another thing than this definition. -/
def switchFresh (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat) : Option (Nat × Nat) :=
  some ((switchSent Z others).size - 1, k)

/-- The main rows of the switch's messages in a run. n: the round's number in the part: the last n
challenges heard are the part's own and are cut off. -/
def switchRowsAt (Z : Sizes) (carries : List (String × Due)) (c : CsAll carries)
    (t : State SwitchAsk Unit) (n : Nat) : Except String (Nat → Nat → Nat → Cb.Gl.E) :=
  (t.input.left (t.heard.take (t.heard.length - n)) (Stretch.carried carries c)).map fun W =>
    mainRows Z W t.input.own

/-- How many entries the rest has: the length of Carrying.lean's own list `rest`, at zeros: it hangs
on the sizes alone. -/
def _root_.VerifiableInference.Desc.K2.Honest.Sizes.restLength (Z : Sizes) : Nat :=
  (rest Z
    ⟨fun _ => zeroG, fun _ => zeroG, fun _ _ => zeroG, fun _ _ => zeroG,
      fun _ => ⟨fun _ _ => zeroG, fun _ _ => zeroG⟩⟩).length

/-- A statement that holds of a switch's sizes what the verifier's test on the target reads of a
statement: the codes, and the kept members' shapes, under the numbers 0, 1, and so on. -/
def _root_.VerifiableInference.Desc.K2.Honest.Sizes.asStatement (Z : Sizes) : OnBytes.Statement :=
  { codes := Z.codes, oracles := (Z.kept.map fun s => ({ shape := s } : OnBytes.Oracle)).toArray }

/-- Single rows that hold of a switch's sizes what that test reads of the carried rows: the two
codes' numbers; two masks; the kept members, under these numbers; the count of their main rows. -/
def _root_.VerifiableInference.Desc.K2.Honest.Sizes.asRows (Z : Sizes) : OnBytes.SingleRows :=
  { code := Z.code, maskCode := Z.maskCode, masks := 2
    keptRows := Z.kept.foldl (fun n s => n + s.mainRows) 0
    layout := { members := Array.range Z.kept.length
                kept := Array.replicate Z.kept.length true } }

/-- **The sizes fit a switch**: THE VERIFIER's OWN TEST ON THE TARGET, CALLED (`switchTargetCheck`,
OnBytes/Iop/Cs.lean), at a statement and single rows made of the sizes; and the rest, as
Carrying.lean lists it, is no longer than the places that the verifier's text counts for it. What
the honest text needs of that test, so that `carrying`, `mainRows` and the laying of a message leave
nothing out in silence: the codes are in their lists; the rest and the folded main row's message
have room; the two blocks are all the rows of the carrying message and share none; each kept copy's
target has its member's rows, field, answers and message length. What the test asks beyond that: the
carrying message lies over the extension field, has a sample, and its pad and each kept member's can
be made; the old code's message length is a power of two; the main block is no longer than it. THAT
THE TEST AT THESE STAND-INS IS THE TEST AT A RUN's OWN STATEMENT AND CARRIED ROWS IS NOT SHOWN. -/
def _root_.VerifiableInference.Desc.K2.Honest.Sizes.roomy (Z : Sizes) : Bool :=
  OnBytes.switchTargetCheck Z.asStatement Z.asRows Z.target &&
    decide (Z.restLength ≤ (OnBytes.SwitchPlaces.make Z.codes Z.target).size)

/-- **The part.** k: the next fold's row variables. A fault, and no message, at a place that
Carrying.lean's `mainRows` does not serve, or whose sizes do not fit a switch. -/
def switchPart (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
    (carries : List (String × Due)) : Part Unit SwitchAsk Unit :=
  { takes := sendingDue Z.codes (switchSent Z others) (switchFresh Z others k), spends := []
    carries := carries
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [
      ⟨fun c _ t =>
          if !Z.serves then .error "the switch's rest does not lie in main rows" else
          if !Z.roomy then .error "the sizes do not fit a switch" else
          (switchRowsAt Z carries c.2.2 t 0).bind fun D =>
          (Sd.tables Z.codes (switchSent Z others) (switchFresh Z others k) D c.1).map fun T =>
            ⟨[], T⟩,
        fun t => t.own⟩,
      ⟨fun c _ t =>
          (switchRowsAt Z carries c.2.2 t 1).bind fun D =>
          (Sd.answers Z.codes (switchSent Z others) (switchFresh Z others k) D c.1
            ((t.lately 1).flatMap (·.elems))).map fun A => ⟨A.map .answer, []⟩,
        fun t => t.own⟩] }

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.Stretch
#print axioms ProofFile.Honest.K2.Stretch.of
#print axioms ProofFile.Honest.K2.Stretch.cut
#print axioms ProofFile.Honest.K2.Stretch.fs
#print axioms ProofFile.Honest.K2.Stretch.es
#print axioms ProofFile.Honest.K2.Stretch.carried
#print axioms ProofFile.Honest.K2.messageDue
#print axioms ProofFile.Honest.K2.foldAt
#print axioms ProofFile.Honest.K2.dueBefore
#print axioms ProofFile.Honest.K2.sendingDue
#print axioms ProofFile.Honest.K2.Sender
#print axioms ProofFile.Honest.K2.SwitchAsk
#print axioms ProofFile.Honest.K2.switchSent
#print axioms ProofFile.Honest.K2.switchFresh
#print axioms ProofFile.Honest.K2.switchRowsAt
#print axioms VerifiableInference.Desc.K2.Honest.Sizes.restLength
#print axioms VerifiableInference.Desc.K2.Honest.Sizes.asStatement
#print axioms VerifiableInference.Desc.K2.Honest.Sizes.asRows
#print axioms VerifiableInference.Desc.K2.Honest.Sizes.roomy
#print axioms ProofFile.Honest.K2.switchPart
