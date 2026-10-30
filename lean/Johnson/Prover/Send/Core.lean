-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Send/Core.lean: THE SHARED "SENDING" (the kind K1: Johnson/Desc/K1/Own.lean), THE
PROVER's SIDE: its core, free of any frame: what a caller hands, what is written. Definitions alone;
no theorem is stated. Every definition has code: none is marked noncomputable.

General in the place: the one public letter is P : K1.Par.
  Rows          what the caller hands of ONE oracle message: every row in full, as field values:
                main rows over E or over F, each with its tail; mask rows with their tails. The
                caller says what every entry is (data, a pad, free room, a mask row's entries).
  Rows.word     its two tables by K1's own index: entry (row r, place j) at r + j * 2 ^ (clog rows);
                0 at a row beyond the real ones
  laidE, laidF  a vector, laid into rows and places by a VectorLay
  held          words grown by the place's messages, at the numbers first, first + 1, ...
  answers       the answers to the sample: for each sampled message, for each answer i, THE LEFT
                SIDE OF K1's OWN sampleRow at the held words, written
  symF          a code word's symbol over F (over E: symG, Johnson/Prover/Link/Base.lean; an
                element's three words: words3, Johnson/Prover/Link/SwitchCols.lean)
  col           the written column of one of the place's trees at a position: for each message in
                the tree, in the order of sending, its main rows' symbols; then, in the same order,
                their mask rows' symbols, at the position modulo the mask code's length

WHAT BINDS THE CALLER. (1) A ROW HOLDS 0 FROM ITS CODE's MESSAGE LENGTH ON: a table has 2 ^ logEll
places a row, and K1's sampleRow has a coefficient at every one; Rows.word hands the caller's entry
there as it is; but symG and symF encode the places below the code's ell alone. So where ell is no
power of two, an entry other than 0 at a place from ell on would stand in an answer and in no code
word. Where ell = 2 ^ logEll (Codes.lengthsOk, OnBytes/Iop/Ground.lean: a public test, which K1's
planOkOwn does not ask) there is no such place. (2) A main row's degree is 1 or 3: mainSyms writes
three words where mainDeg is 3 and one word else; the program's columnOf reads one word where it is
1 and three else: the two part at any other number, which the shapes' test refuses.
On (1): K1.Msg.pad (Johnson/Desc/K1/Own.lean) counts the pad's places back from 2 ^ logEll,
Own.padMade (Johnson/Desc/Own/Send.lean) from the code's ell: at a length that is no power of two
K1's row reads the pad at a place where (1) lays 0. SendFront (Front.lean) does not ask
Codes.lengthsOk: SendFront.of_lengths (Form.lean) goes from it to SendFront, not back.
Codes.lengthsOk is a premise of, among others, front6_whole (Johnson/Prover/Link/FormSendGave.lean),
front6_all (FormFront6More.lean) and front6_walks (FormWalks.lean); in this folder
SendFront.of_lengths has it as a premise.

What is not here. No root: a view shows none, and the tree is the compiler's. No coin, no
distribution, no order of coins. No statement: that K1's decision says yes on these, that the sample
rows hold, and that col is what the description reads of a tree, are stated in the files beside this
one (Johnson/Prover/Send/Form.lean, Johnson/Prover/Send/Says.lean,
Johnson/Prover/Send/Enc.lean). The sending inside a code switch is another
text of the description's and has another writer (Johnson/Prover/Link/SwitchMsg.lean). Nothing on
what any entry discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Own
import Johnson.Desc.Means.Says
import OnBytes.Slice.BlkRead
import OnBytes.Slice.ProgCodes
import Johnson.Prover.Link.SwitchCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open Johnson.Prover.Link (symG words3)

/-- **What the caller hands of one oracle message.** Row, then place. THE CALLER LAYS 0 AT EVERY
PLACE FROM THE ROW's CODE's MESSAGE LENGTH ON (the head says why). -/
structure Rows where
  mainE : ℕ → ℕ → GE
  mainF : ℕ → ℕ → GF
  mainTlE : ℕ → ℕ → GE
  mainTlF : ℕ → ℕ → GF
  mask : ℕ → ℕ → GE
  maskTl : ℕ → ℕ → GE

/-- A main entry, in E: mainE where overE, else mainF; the other field is not read. -/
def Rows.main (R : Rows) (overE : Bool) (r j : ℕ) : GE :=
  if overE then R.mainE r j else algebraMap GF GE (R.mainF r j)

/-- The message's two tables by index. -/
def Rows.word (R : Rows) (s : OracleShape) : Part → ℕ → GE
  | .main, i =>
    if i % 2 ^ K1.clog s.mainRows < s.mainRows then
      R.main (s.mainDeg == 3) (i % 2 ^ K1.clog s.mainRows) (i / 2 ^ K1.clog s.mainRows) else 0
  | .mask, i =>
    if i % 2 ^ K1.clog s.maskRows < s.maskRows then
      R.mask (i % 2 ^ K1.clog s.maskRows) (i / 2 ^ K1.clog s.maskRows) else 0

/-- A vector as rows and places: entry (row r, place j) is the vector's entry at the table's index
r + j * 2 ^ rowBits. -/
def laidE (lay : VectorLay) (v : ℕ → GE) : ℕ → ℕ → GE :=
  fun r j => v (lay.entryAt (r + j * 2 ^ lay.rowBits))
def laidF (lay : VectorLay) (v : ℕ → GF) : ℕ → ℕ → GF :=
  fun r j => v (lay.entryAt (r + j * 2 ^ lay.rowBits))

/-- The shape of message number k of the place. -/
def shapeAt (P : K1.Par) (k : ℕ) : OracleShape := (P.sent.getD k default).shape

/-- **The held words**, grown by the place's messages. -/
def held (w : Words GE) (first : ℕ) (P : K1.Par) (V : ℕ → Rows) : Words GE :=
  fun o part i =>
    if first ≤ o ∧ o < first + P.sent.size then (V (o - first)).word (shapeAt P (o - first)) part i
    else w o part i

/-- **The answers**, in the order in which K1's layRows takes them. S': the statement that has
received the messages. Where seeds has no entry number i, seeds.getD i default is read; nothing
refuses here. -/
def answers (P : K1.Par) (S' : Statement) (first : ℕ) (w' : Words GE)
    (seeds : List (List E × E)) : List Fmt.Ext3 :=
  ((List.range P.sent.size).filter fun k => (shapeAt P k).answers != 0).flatMap fun k =>
    (List.range (shapeAt P k).answers).map fun i =>
      ofE (value rdE S'
        (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) (seeds.getD i default).1
          (seeds.getD i default).2 i zeroE) w')

/-- A code word's symbol over F: the value, at the position's point, of the polynomial whose
coefficients are the tail's entries and then the message's. At C.r = 0 the first sum is empty: no
entry of the tail is read; nothing refuses. -/
def symF (C : Fmt.M1.Code) (x : ℕ) (m r : ℕ → GF) : GF :=
  (∑ q ∈ Finset.range C.r, toF (Fmt.M1.point C.a x) ^ q * r q) +
    ∑ j ∈ Finset.range C.l, toF (Fmt.M1.point C.a x) ^ (C.r + j) * m j


/-- The main rows' symbols of message number k at x. -/
def mainSyms (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) : List UInt64 :=
  let s := shapeAt P k
  let C := codeOf (P.codes.base.getD s.code default)
  (List.range s.mainRows).flatMap fun r =>
    if s.mainDeg == 3 then words3 (ofE (symG C x ((V k).mainE r) ((V k).mainTlE r)))
    else [ofF (symF C x ((V k).mainF r) ((V k).mainTlF r))]

/-- The mask rows' symbols of message number k at x. -/
def maskSyms (P : K1.Par) (V : ℕ → Rows) (k x : ℕ) : List UInt64 :=
  let s := shapeAt P k
  let Z := codeOf (P.codes.mask.getD s.maskCode default)
  (List.range s.maskRows).flatMap fun r =>
    words3 (ofE (symG Z (x % 2 ^ Z.a) ((V k).mask r) ((V k).maskTl r)))

/-- **The written column** of tree number tree of the place, at the position x. -/
def col (P : K1.Par) (V : ℕ → Rows) (tree x : ℕ) : List UInt64 :=
  let lay := (Own.treesMade P.codes P.sent).getD {}
  let mine := (List.range P.sent.size).filter fun k => lay.tree[k]? == some tree
  (mine.flatMap fun k => mainSyms P V k x) ++ mine.flatMap fun k => maskSyms P V k x

end Johnson.Prover.Send
