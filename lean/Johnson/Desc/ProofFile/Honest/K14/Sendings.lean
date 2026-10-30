-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/Sendings.lean: the honest side of the two sendings of the batch's
shared rounds, "send o_u" and "send o_omega", in the form of Honest/Frame.lean. Definitions with
code, on the program's own elements; no theorem.

What is sent. A sending has two rounds and is one part. In "SEND seed" the prover sends no item in
the clear and, for each root, the oracle message beneath it: a table whose symbol at a position
holds, for each message in that tree in the order of sending, the symbols of its main rows' code
words, and then, in the same order, the symbols of their mask rows' code words at the position
modulo the mask code's length. In "SEND answer" it sends, for each sampled message, its
out-of-domain (OOD) answers: the left side of the message's own sample row
(Johnson/Desc/K1/Own.lean: sampleRow) at its tables. "send o_u" sends o_u, whose main table carries
the folded row (uAtE, Johnson/Desc/K14/Honest/Coded.lean), and, WHERE MASKS ARE SENT AHEAD
(LinShape.masksAhead), the first mask of the proximity test on G_u. "send o_omega" sends o_omega,
whose main table carries omega_col (omegaAtE), and, WHERE THE SHAPE SPLITS
(LinShape.sharedSplitNeeded), the split's mask message o_sp. Without them a sending has its first
message alone. WHERE MASKS ARE SENT AHEAD AND THE TEST ON G_u HAS NO STAGE, "send o_u" HAS NO
MESSAGE AT ALL.

The coins. A part takes its own, all of the extension field, message by message in the order of
sending; in a message: the main rows' tails, row 0 first; the pad of its OOD sample, if it lies in a
main row; all entries of the mask rows, entry c of row r of m rows at the number c m + r; the mask
rows' tails. A FOLD's FRESH TABLE, which the first mask is, is laid otherwise: its coins are the
2 k + 1 coefficients of the fold's hiding polynomial, by variable, in a variable by rising degree:
degrees 1 and 2 for every variable but the last, degrees 0, 1 and 2 for the last; and then its rows'
tails. Its entries are these coefficients as the format's model prover packs them (Fmt/M1Fold.lean:
FoldOwn.freshRow), and 0 beyond. A place of the pad holds a coin, never the vector's placeholder 0.
No part here spends or carries a coin of another part, and none has a stop.

  MsgSort     what a message is laid of: a vector and coins, or a fold's hiding polynomial
  dueOf, offsetOf, takesOf   how many coins a message takes; where they begin; a sending's count
  Laid, laid  one message's rows in full, of its vector and its coins
  wordsOf     the sending's tables by the message's number in the sending, part and index
  symbolsOf, columnOf, sentTables   the code words' symbols (Fmt.M1.symE, the format's own); a
              tree's column at a position; the tables
  localOf     a statement that holds the sending's messages alone: for the tables' sizes
  answersOf   the OOD answers
  SendJob, sendingPart   a sending's public data and vectors; the part
  SendPub, jobU, jobOmega, proverSidesOfSharedSendings   the two sendings, and their halves lifted to the shared
              chain's type parameters

What the parts read. Of the input: the committed table's rows before encoding (Ask.rows, as
Honest/K14/Parts.lean makes them: the index's entries, and the committer's pads and tails, which are
read through TableRand, Honest/ForKinds.lean). "send o_omega"'s vector asks these rows at the
matrix's places alone, where they hold the index's entries: NO PAD AND NO TAIL OF THE COMMITTED
TABLE; "send o_u"'s asks them at every place below the folded row's length. Of the challenges:
psi_sh, by its number among the chain's rounds, and the sending's own OOD seeds. No witness, no
instance, no key.

Limits. Written for messages whose main rows are over the extension field, as those of o_u and
o_omega are at a shape that sendingsFit accepts (there the first mask and o_sp have no main row): a
main row over the base field would be laid wrongly. A message with main rows and no OOD answer (a
masking word) is not treated. Free places of a main row hold the vector's placeholder 0. The symbols
are computed by the model encoder of Fmt/M1Codes.lean, whose points are the program's for codes of
at most 2 ^ 32 positions. MET BY A DEFAULT VALUE IN SILENCE (no move returns an error): a coin or a
seed beyond the count; trees that cannot be laid; the point psi_sh, which jobU and jobOmega read by
heardFrom (Honest/ForKinds.lean): where fewer challenges have been heard it is a shorter list (that
file's heardJust would refuse); a code's number beyond its array: the default code: its rows have no
place and no tail, while the coins of a pad or of a fresh table are still counted and are laid
nowhere; a message's number beyond the sending: the default shape; a word beyond a column's length:
0; masks sent ahead and no stage in the test on G_u: "send o_u" is a sending of no message, not of
o_u either ((7) of sendingsFit rejects it). ONE PUBLIC TEST WITH CODE IS MEANT TO ACCEPT ONLY SHAPES
AT WHICH THE PARTS LAY A COIN WHEREVER A COIN IS DUE: sendingsFit, Honest/K14/SendingsShapes.lean:
every law on a coin of these parts is to take it as a named premise; that it accepts no other shape
is proved neither in this file nor in any file that it imports; that the vectors fit their main rows
it does not ask. proverSidesOfSharedSendings hands the parts
the rows of rowsOf (Honest/K14/Parts.lean) AND ASKS NO TEST, not even the library's test on the
linear part's shape (LinShape.ok, OnBytes/Iop/Lin.lean): where the matrix's places reach into the
pads these rows
are not the committed rows' text. OTHER TEXTS OF THE SAME SENDINGS STAND IN THIS LIBRARY, over its
fields: Johnson/Prover/Send/Core.lean (Rows.word, laidE, answers, col: the like of wordsOf, of laid
at a vector, of answersOf and of columnOf) and Johnson/Desc/K14/Honest/SendMoves.lean (vecMain,
sendsU, sendsOmega: the like of laid's main rows with jobU and jobOmega). NOTHING IN THIS FILE HOLDS
THE TEXTS TOGETHER. Nothing on any property.

CASES THAT HANG ON PUBLIC DATA, MET IN SILENCE TOO. This file has no statement that bars them.
  * laid's subtractions on natural numbers, which truncate at 0: c.ell - s.answers at a plain
    message; l - 1, t - 1 and k - 1 at a fold's fresh table. Where they truncate, one coin stands at
    two places or a counted coin is laid nowhere
  * A fresh table's row has 2 k - h + 1 coefficients and the encoder reads a row's first places up
    to the mask code's message length: a shorter code would drop the last coefficients in silence
  * a message that lies in no tree, whose rows columnOf would leave out
  * a vector that does not fit its main rows is cut, and where the matrix's places reach into the
    pads an entry of the matrix is laid for a pad (rowsOf; the vectors' own texts,
    Johnson/Desc/K14/Honest/Coded.lean). That the library's test on the linear part's shape and
    codes (OnBytes.linOk) bars both is a reading of its text; this file has no theorem on it

CASES THAT HANG ON A RUN, MET IN SILENCE. This file has no statement on them.
  * A POINT THAT IS NOT WHOLE. splitValue (Honest/K14/Parts.lean), jobU and jobOmega read challenges
    by heardFrom (Honest/ForKinds.lean), which returns a shorter list where fewer have been heard;
    and the vectors' texts take and drop elements of the point, so that a point of too few elements
    gives other weights in silence. What would bar it: that at each of these parts' rounds the
    challenge of "LIN point" (at "SPLIT" that of "LIN zeta" too) has been heard and holds as many
    elements as the shape counts. This file does not state that.
  * SEEDS THAT ARE NOT WHOLE. K1.cutSeeds cuts the seeds off the elements of the last challenge
    (State.lately); where these are too few a seed's point is shorter and its factor is 0. Under the
    test on the challenges' form neither happens: draws_send (Johnson/SendSim/At/SeatedAt.lean).

ZEROS THAT ARE NO DEFAULT OF AN ERROR. They are sent or committed as they stand. Neither this file
nor any file that it imports has a statement that holds them against the format's pages.
  * AT REAL PLACES OF A MASK ROW: a fold's fresh table (the first mask, sent with o_u) holds the
    coefficients of the hiding polynomial and 0 at its other places (laid's arm for a fresh table;
    Fmt.M1.FoldOwn.freshRow, Fmt/M1Fold.lean); neither this file nor any file that it imports has a
    theorem that says at which places
  * the free places of a main row: the vectors' own texts return 0 beyond their entries
    (Johnson/Desc/K14/Honest/Coded.lean)
  * wordsOf's 0 at the rows beyond the real ones, which an answer reads wherever the number of rows
    is no power of two
  * rowsOf's 0 in three zones of a committed row: between the matrix's entries and the pads; between
    the code's message length and the first tail; beyond the fold's entries. entriesOf, which the
    four halves of Honest/K14/Parts.lean are handed, is 0 at the pads and the tails too; that these
    four read the matrix's places alone is said in the head of Honest/K14/Parts.lean, by reading

No statement in this file says that these lists are complete, or that a coin below the count is
read.
-/
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K14.Law.SaysTests
import Fmt.M1Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE Codes OracleShape OracleNotice Statement vectorLay ceilLog2)
open OnBytes.Means (Words)
open OnBytes.Slice (toE toF)
open VerifiableInference.Desc (Place K1.Par K1.sampleRow K1.Msg.of K1.cutSeeds)

variable {W₀ Rc Ky X : Type}

/-! ## The coins of a sending, in order -/

/-- **What a message is laid of.** plain: its main table carries a vector, laid with the rows'
number high or low (OnBytes/Iop/Foldeq.lean: vectorLay); every entry of a mask row is a coin.
fresh k h: a fold's fresh table: 2 ^ h mask rows that hold the hiding polynomial of a fold of k
variables. -/
inductive MsgSort where
  | plain (high : Bool)
  | fresh (k h : Nat)

/-- How many coins, all of the extension field, a message of this shape takes. -/
def dueOf (codes : Codes) (s : OracleShape) : MsgSort → Nat
  | .plain _ =>
    s.mainRows * (codes.base.getD s.code default).r + (if s.maskRows == 0 then s.answers else 0) +
      s.maskRows * (codes.mask.getD s.maskCode default).ell +
      s.maskRows * (codes.mask.getD s.maskCode default).r
  | .fresh k _ => 2 * k + 1 + s.maskRows * (codes.mask.getD s.maskCode default).r

/-- The number of the first coin of message number k. -/
def offsetOf (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) (k : Nat) : Nat :=
  (sent.toList.take k).zipIdx.foldl (fun n x => n + dueOf codes x.1.shape (sort x.2)) 0

/-- A sending's count. -/
def takesOf (codes : Codes) (sent : Array OracleNotice) (sort : Nat → MsgSort) : Due :=
  ⟨0, offsetOf codes sent sort sent.size⟩

/-! ## One message's rows -/

/-- One oracle message's rows in full. Row, then place. -/
structure Laid where
  main : Nat → Nat → E
  mainTail : Nat → Nat → E
  mask : Nat → Nat → E
  maskTail : Nat → Nat → E

/-- **A message's rows**, of the vector v that its main table carries and of its coins cs, numbered
from 0. -/
def laid (codes : Codes) (s : OracleShape) (v cs : Nat → E) : MsgSort → Laid
  | .fresh k h =>
    let z := codes.mask.getD s.maskCode default
    let U : Fmt.M1.FoldOwn.Hide :=
      ⟨fun l t => (cs (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t)).triple,
        (cs (2 * (k - 1))).triple⟩
    { main := fun _ _ => zeroE, mainTail := fun _ _ => zeroE
      mask := fun r j => E.ofTriple ((Fmt.M1.FoldOwn.freshRow .two k h U r).getD j Fmt.Fld.zeroE)
      maskTail := fun r t => cs (2 * k + 1 + r * z.r + t) }
  | .plain high =>
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  let lay := vectorLay codes s high
  let atPad := s.mainRows * c.r
  let atMask := atPad + (if s.maskRows == 0 then s.answers else 0)
  let atTail := atMask + s.maskRows * z.ell
  { main := fun r j =>
      if s.maskRows == 0 && r + 1 == s.mainRows && decide (c.ell - s.answers ≤ j) &&
          decide (j < c.ell) then cs (atPad + (j - (c.ell - s.answers)))
      else v (lay.entryAt (r + j * 2 ^ lay.rowBits))
    mainTail := fun r t => cs (r * c.r + t)
    mask := fun r j => cs (atMask + j * s.maskRows + r)
    maskTail := fun r t => cs (atTail + r * z.r + t) }

/-- **The sending's tables**: by the message's number in the sending, part and index. In an index
the row's number is the low part. A row beyond the real ones holds 0. -/
def wordsOf (sent : Array OracleNotice) (L : Nat → Laid) : Words E := fun o part i =>
  let s := (sent.getD o default).shape
  match part with
  | .main =>
    if i % 2 ^ ceilLog2 s.mainRows < s.mainRows then
      (L o).main (i % 2 ^ ceilLog2 s.mainRows) (i / 2 ^ ceilLog2 s.mainRows) else zeroE
  | .mask =>
    if i % 2 ^ ceilLog2 s.maskRows < s.maskRows then
      (L o).mask (i % 2 ^ ceilLog2 s.maskRows) (i / 2 ^ ceilLog2 s.maskRows) else zeroE

/-! ## What lies beneath a root -/

/-- The symbols, at the position x, of n rows under a code: three words a row. -/
def symbolsOf (c : OnBytes.Code) (x n : Nat) (row tail : Nat → Nat → E) : List UInt64 :=
  (List.range n).flatMap fun r =>
    let y := Fmt.M1.symE ⟨c.logN, c.ell, c.r⟩ x ((List.range c.ell).map fun j => (row r j).triple)
      ((List.range c.r).map fun t => (tail r t).triple)
    [y.1, y.2.1, y.2.2]

/-- **The column of the sending's tree number tree at the position x.** -/
def columnOf (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) (tree x : Nat) :
    List UInt64 :=
  let lay := (VerifiableInference.Desc.Own.treesMade codes sent).getD {}
  let mine := (List.range sent.size).filter fun k => lay.tree[k]? == some tree
  (mine.flatMap fun k =>
      let s := (sent.getD k default).shape
      symbolsOf (codes.base.getD s.code default) x s.mainRows (L k).main (L k).mainTail) ++
    mine.flatMap fun k =>
      let s := (sent.getD k default).shape
      let z := codes.mask.getD s.maskCode default
      symbolsOf z (x % 2 ^ z.logN) s.maskRows (L k).mask (L k).maskTail

/-- **The tables**, one for each tree that the sending's messages make. -/
def sentTables (codes : Codes) (sent : Array OracleNotice) (L : Nat → Laid) : List Table :=
  ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList.zipIdx.map fun t =>
    { logLength := t.1.logN, words := t.1.mainWidth + t.1.maskWidth
      sym := fun x i => toF ((columnOf codes sent L t.2 x).getD i.val 0) }

/-! ## The OOD answers -/

/-- A statement that holds the sending's messages alone, numbered from 0: for the tables' sizes. -/
def localOf (codes : Codes) (sent : Array OracleNotice) : Statement :=
  { codes := codes, groups := #[], oracles := sent.map fun n => { shape := n.shape } }

/-- **The OOD answers**, in the order of sending; a sampled message's answers in the seeds' order:
each the left side of the message's own sample row at the tables. -/
def answersOf (Q : K1.Par) (L : Nat → Laid) (seeds : List (List E × E)) : List E :=
  ((List.range Q.sent.size).filter fun k => (Q.sent.getD k default).shape.answers != 0).flatMap
    fun k =>
      (List.range (Q.sent.getD k default).shape.answers).map fun i =>
        Desc.K14.Law.valueE (localOf Q.codes Q.sent)
          (K1.sampleRow (K1.Msg.of Q.codes (Q.sent.getD k default).shape) k
            (seeds.getD i default).1 (seeds.getD i default).2 i zeroE) (wordsOf Q.sent L)

/-! ## The part -/

/-- **A sending's public data and vectors.** -/
structure SendJob where
  Q : K1.Par
  /-- for each message: what it is laid of -/
  sort : Nat → MsgSort
  /-- for each message: the vector that its main table carries: of the input and the challenges
  heard -/
  data : State Ask Unit → Nat → Nat → E

/-- The rows of all messages, of the state and the part's own coins. -/
def SendJob.rows (J : SendJob) (t : State Ask Unit) (cs : Array E) (k : Nat) : Laid :=
  laid J.Q.codes (J.Q.sent.getD k default).shape (J.data t k)
    (fun i => cs.getD (offsetOf J.Q.codes J.Q.sent J.sort k + i) zeroE) (J.sort k)

/-- **A sending with the round that holds its answers**: one part of two rounds. -/
def sendingPart (J : SendJob) : Part Empty Ask Unit :=
  { takes := takesOf J.Q.codes J.Q.sent J.sort, spends := [], carries := []
    bad := fun _ _ => none, hid := fun v => nomatch v
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      [⟨fun c _ t => .ok ⟨[], sentTables J.Q.codes J.Q.sent (J.rows t (coinsE c.1).toArray)⟩,
          fun t => t.own⟩,
       ⟨fun c _ t => .ok ⟨(answersOf J.Q (J.rows t (coinsE c.1).toArray)
            (K1.cutSeeds J.Q.coordinates J.Q.seeds (elems (t.lately 1)))).map
              fun y => .answer (toE y.triple), []⟩,
          fun t => t.own⟩] }

/-! ## The two sendings -/

/-- **The public data of the two sendings**: the shared chain's own parameters, and the number, from
0, among the chain's rounds, of "LIN point". -/
structure SendPub where
  P : Desc.K14.P14
  atPoint : Nat

/-- "send o_u". -/
def jobU (A : SendPub) : SendJob :=
  { Q := Desc.K14.parK1 A.P 2 "o_u and the first mask" ((Desc.K14.withU A.P.S).getD #[])
    sort := fun k =>
      if k == 0 then .plain A.P.S.fold.rowsHigh
      else match A.P.S.testU.head? with
        | some s => .fresh s.k s.h
        | none => .plain false
    data := fun t _ => Desc.K14.Honest.uAtE A.P.S (elems (heardFrom t A.atPoint 1)) t.input.rows }

/-- "send o_omega". -/
def jobOmega (A : SendPub) : SendJob :=
  { Q := Desc.K14.parK1 A.P 5 "o_omega and o_sp" (Desc.K14.withOmega A.P.S)
    sort := fun _ => .plain A.P.S.omegaRowsHigh
    data := fun t _ =>
      Desc.K14.Honest.omegaAtE A.P.S (elems (heardFrom t A.atPoint 1)) t.input.rows }

/-- A sending's place at a piece of the shared chain. -/
def sendPlace (piece : Nat) : Place := ⟨2, none, piece, .K1⟩

/-- **The two halves**, lifted. weights, rand: they read the index and the index committer's coins
off the input. -/
def proverSidesOfSharedSendings (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    List (Placed Empty (Common W₀ Rc Ky) X) :=
  let lifted (p : Part Empty Ask Unit) : Part Empty (Common W₀ Rc Ky) X :=
    p.lift (fun v => v) (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩) (fun _ => ())
      fun x _ => x
  [⟨sendPlace 2, [lifted (sendingPart (jobU A))]⟩,
   ⟨sendPlace 5, [lifted (sendingPart (jobOmega A))]⟩]

end ProofFile.Honest.K14
