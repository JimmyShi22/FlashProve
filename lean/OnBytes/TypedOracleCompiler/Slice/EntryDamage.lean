-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryDamage.lean: DAMAGE BEHIND THE CONVERTER: PLAIN COMPUTABLE FUNCTIONS THAT
TURN ONE THING OF THE ENTRY's TYPED STRING, AT A PLACE GIVEN BY NUMBERS, SO THAT THE VERIFIER ALONE
(runE | runJE's second half: verifyLX) IS RUN ON A DAMAGED STRING. NOT HONEST BY DESIGN: every
function here makes an ALTERED input for a verifier. NOTHING IS PROVED. It makes altered inputs, for
tests that a verifier must refuse.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY: with the port's own reader as the converter every damaged FILE is refused by the converter: the
compiler's verifier never sees it. All trust lies in the verifier: so it must be shown damaged TYPED
values: (d7) to (d14).
TWO KINDS. (S) ON THE STRING: OneProtocolProof 256 (PSXE D dec).up → the same type. (O) ON THE CHAIN AS READ:
Fmt.ChainOut → Fmt.ChainOut, TO BE APPLIED BEFORE assembleS: for (d7), (d8) and the own half of
(d14): a plain part's type hangs on the round's items, an own symbol's on its tree: there the turn
is written where the value is still a list; assembleS carries it into exactly one field of the
string (plains; plains; opens).
  PLACES. An own position: (t, x) := (THE FORM's OWN NUMBER s.tree, the leaf's number). A stored
    one: (w, x) := (0 | 1: which table, the leaf's number). ownPlaces o | storedPlaces D o list
    those that the honest file opens: TURN AT A LISTED PLACE, or nothing is turned.
  (d7)  O.val k j          round k's j-th value: 1 is added to its (first) word; a root is left as
    it is
  (d8)  O.nonce k          round k's nonce: 1 is added
  (d9)  S.addOneToWordAtOwnOpening t x i    word i of the column at the own position (t, x): 1 is added
  (d10) S.stoWord w x i    word i of the column at the stored position (w, x): 1 is added
  (d11) S.ownPath t x l | S.stoPath w x l     bit 0 of the l-th digest of that opening's path is
    flipped (l = 0: the leaf's sibling)
  (d12) S.ownSalt t x | S.stoSalt w x         the last bit of that opening's typed salt (the file's
    salt's last bit) is flipped
  (d13) S.salt             bit 0 of the string's salt (the chain's run value as bits) is flipped;
    the typed salts of leaves are not touched
  (d15) S.stoShift w x     the stored opening at (w, x): the file's salt's first eight bytes go to
    the column's end
  (d14) S.stoSwap w x y    the openings at the stored positions (w, x) and (w, y) are exchanged
    whole;   O.ownSwap k t i j: in round k's t-th opening the i-th and j-th (column, salt) are
    exchanged
TWO ENDINGS BEFORE afterB's CLAUSES, WHICH A RUNNER MUST TELL APART: (i) assembleS REFUSES the
turned chain (kind (O)): THEN THE VERIFIER IS NOT RUN: no test of it; foretold for none of the
three: assembleS tests no value's range, no nonce, and the exchanged columns have one width; (ii)
chainP itself refuses (Run/LaxWhy.lean's "chain"): by its text only where the string has too few
roots or the phase allows no act (actOf: a matter of the rounds' marks and the phase, which no turn
touches): none of the turns takes a root away: foretold for none. Run/LaxWhy.lean: whyLX names the
clause.
FORETOLD, BEFORE ANY RUN: EACH IS REFUSED; BY WHICH CLAUSE OF verifyLX (afterB's order: own |
ext are some; few; formed; walks; request tree; accept):
  (d7), (d8) at round k: round k's query holds round k's OWN plain part (message, nonce), and ROUND
    k's OWN verifier's message is made of its answer (chainP's text, Run/ThinDefs.lean:188-199): so
    round k's draws change, and every later round's: IF ROUND k OR A LATER ROUND DRAWS POSITIONS:
    other positions are read than the string opens: "own" or "ext" is none: NO AT THE FIRST CLAUSE
    THAT FAILS ("own" is asked first). [A chance of about (listed places / all places)^(positions
    drawn) that the new draws fall on opened places alone: nothing.] ONLY BEHIND THE LAST ROUND THAT
    DRAWS POSITIONS do the reads stand: then NO AT "accept". SO A TURNED NONCE DOES NOT SHOW THE
    WORK's TEST (passSL, a conjunct of accept, evaluated last): Slice/EntryProbe.lean's workE
    evaluates it by itself. (d8) AT A ROUND WITHOUT WORK: NOT FORETOLD: whether the typed query
    holds the nonce there was not read.
  (d9), (d10), (d12): the leaf's query changes: its digest: the climb ends elsewhere: NO AT "walks".
    (d11): the climb takes another sibling: NO AT "walks".
  (d13): the first query (.f1) holds the salt: the first chain value changes: all draws: NO AT "own"
    | "ext" (none).
  (d14): at each of the two places stands the other's column: NO AT "walks" (a stored symbol carries
    its place: symbolsCarryTheirPositions in "accept" would refuse it too, but is not reached).
  (d15) S.stoShift w x [on a counter-example: "move the salt's first 8 bytes to the column's end:
    the same Fmt.formatHash call"]: the stored opening's column gets one word more, which is the file's
    salt's first eight bytes; the typed salt loses them: column and salt TOGETHER spell the same
    bytes. FORETOLD: NO AT "walks", UNDER THE FAST FAMILY TOO: the counter-example is of a typed
    QUERY (a body eight bytes longer); a STRING reaches a leaf's body only through embE (place,
    column), and by stoE_law the body spells, in the label's word, THE NUMBER OF THE COLUMN's WORDS
    (Fmt.leafPlace tree col.length …): one more: another call, another digest. [GROUND:
    StringsStoredAt.lean, ok2_rd2_embX's STATEMENT: rd2 (embX a salt c y) = (174, Fmt.leafPlace 0
    y.2.length (salt / 8), 2 ^ a + y.1, Fmt.colBytes y.2 ++ Fmt.zeroBytes (Fmt.fillLen y.2.length
    salt)): THE COLUMN's WIDTH STANDS IN THE LABEL, and a fill may stand between column and salt;
    famFastE hashes what rd2 reads (not shown here). SO AT BOTH FAMILIES (famFastE | a family
    that refuses where the page does not write): NO AT "walks". "Under famFastE the walk passes" is
    true of the QUERY, not of a string's leaf. Where storedOK fails of the longer column embX goes
    behind its escape: another body still. IF IT IS ACCEPTED: AN ALARM, AND THE COUNTER-EXAMPLE IS
    LIVE AT STRINGS.] The test askedJE (a file of this project that is not in this library) with
    goodE should say false at it or
    the walk fail: not foretold which.
  AN ACCEPT OF ANY IS AN ALARM.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryTyping

set_option autoImplicit false

namespace TypedOracleCompiler.Slice.Damage
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Run.PQ (View SgX)

/-! ## Small turns -/

def flipD (d : Dig 256) : Dig 256 := fun i => if i.val = 0 then !d i else d i
def flipFirst : Bits → Bits
  | [] => []
  | x :: r => (!x) :: r
def flipLast (b : Bits) : Bits := (flipFirst b.reverse).reverse
/-- f at the i-th member of a list -/
def atL {α : Type} (i : ℕ) (f : α → α) (l : List α) : List α := l.zipIdx.map fun z =>
    if z.2 = i then f z.1 else z.1
/-- the i-th and the j-th member exchanged -/
def swapL {α : Type} (i j : ℕ) (l : List α) : List α :=
  l.zipIdx.map fun z => if z.2 = i then (l[j]?).getD z.1 else if z.2 = j then
      (l[i]?).getD z.1 else z.1

/-! ## The places that the honest file opens -/

def ownPlaces (o : _root_.Fmt.ChainOut) : List (ℕ × ℕ) :=
  ((opsOf 1 o).filter fun op => !op.sh.stored).flatMap fun op => op.xs.map fun x => (op.sh.tree, x)
def storedPlaces (D : XD) (o : _root_.Fmt.ChainOut) : List (ℕ × ℕ) :=
  ((opsOf 1 o).filter fun op => op.sh.stored).flatMap fun op => op.xs.map fun x => (whichOf D op, x)

/-! ## (O) On the chain as read -/

namespace O

def round (k : ℕ) (f : _root_.Fmt.RoundOut → _root_.Fmt.RoundOut) (o : _root_.Fmt.ChainOut) :
    _root_.Fmt.ChainOut :=
  { o with rounds := (atL k f o.rounds.toList).toArray }

def got : _root_.Fmt.ItemValue → _root_.Fmt.ItemValue
  | .f x => .f (x + 1)
  | .e x => .e (x.1 + 1, x.2)
  | .word x => .word (x + 1)
  | .root d => .root d
  | .answer x => .answer (x.1 + 1, x.2)

/-- (d7) -/
def val (k j : ℕ) : _root_.Fmt.ChainOut → _root_.Fmt.ChainOut := round k fun r =>
    { r with vals := atL j got r.vals }
/-- (d8) -/
def nonce (k : ℕ) : _root_.Fmt.ChainOut → _root_.Fmt.ChainOut := round k fun r =>
    { r with nonce := r.nonce + 1 }
/-- (d14), own -/
def ownSwap (k t i j : ℕ) : _root_.Fmt.ChainOut → _root_.Fmt.ChainOut := round k fun r =>
  { r with opens := atL t (fun y =>
      let oo : _root_.Fmt.OpenOut := y.2.2
      (y.1, y.2.1, { oo with cols := swapL i j oo.cols, salts := swapL i j oo.salts })) r.opens }

end O

/-! ## (S) On the string -/

/-- a turn of an own opening, told the tree's form and the leaf's number -/
abbrev Turn : Type :=
  (s : _root_.Fmt.Shape) → Fin (2 ^ s.a) → Opening 256 (Fin s.W → UInt64) →
      Opening 256 (Fin s.W → UInt64)

def mapT (f : Turn) : (ts : List _root_.Fmt.Shape) → (p : PQ.PosT ts) → Opening 256 (PQ.SymT ts p) →
    Opening 256 (PQ.SymT ts p)
  | s :: _, .inl x, op => f s x op
  | _ :: ts, .inr p, op => mapT f ts p op

def mapL (C : PQ.CK) (f : Turn) : (ds : List PQ.RD) → (p : OPos (PQ.uL C ds)) →
    Opening 256 (OSym (PQ.uL C ds) p) →
    Opening 256 (OSym (PQ.uL C ds) p)
  | [], p, _ => p.elim
  | d :: _, .inl p, op => mapT f d.trees p op
  | _ :: ds, .inr q, op => mapL C f ds q op

namespace S
variable {X : Type} {D : XD} {dec : X → View → Bool}

/-- every own opening through f -/
def own (f : Turn) (π : OneProtocolProof 256 (PSXE D dec).up) : OneProtocolProof 256 (PSXE D dec).up :=
  { π with opens := fun p => match p with
      | .inl e => e.elim
      | .inr q => (π.opens (.inr q)).map (mapL D.C f D.ds q) }

/-- is this external position number x of table w? -/
def isAt (w x : ℕ) : Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a) → Bool
  | .inl q => w == 0 && q.val == x
  | .inr q => w == 1 && q.val == x

/-- the external opening at (w, x) through f -/
def sto (w x : ℕ) (f : Opening 256 SgX → Opening 256 SgX) (π : OneProtocolProof 256 (PSXE D dec).up) :
    OneProtocolProof 256 (PSXE D dec).up :=
  { π with ext := fun p => if isAt (D := D) w x p then (π.ext p).map f else π.ext p }

/-- (d9) -/
def addOneToWordAtOwnOpening (t x i : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  own fun s y op => if s.tree = t ∧ y.val = x then { op with sym := fun k => if k.val = i then op.sym k + 1 else op.sym k } else op
/-- (d10) -/
def stoWord (w x i : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  sto w x fun op => { op with sym := (op.sym.1, atL i (· + 1) op.sym.2) }
/-- (d11) -/
def ownPath (t x l : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  own fun s y op => if s.tree = t ∧ y.val = x then { op with path := atL l flipD op.path } else op
def stoPath (w x l : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  sto w x fun op => { op with path := atL l flipD op.path }
/-- (d12) -/
def ownSalt (t x : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  own fun s y op => if s.tree = t ∧ y.val = x then { op with salt := flipLast op.salt } else op
def stoSalt (w x : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  sto w x fun op => { op with salt := flipLast op.salt }
/-- (d15): the file's salt's first eight bytes moved to the column's end -/
def stoShift (w x : ℕ) : OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up :=
  sto w x fun op =>
    let rest := op.salt.drop 256
    { op with sym := (op.sym.1, op.sym.2 ++ [_root_.Fmt.wordAt (_root_.Run.bitsToBytes (rest.take 64)) 0]),
              salt := op.salt.take 256 ++ rest.drop 64 }
/-- (d13) -/
def salt (π : OneProtocolProof 256 (PSXE D dec).up) : OneProtocolProof 256 (PSXE D dec).up :=
    { π with salt := flipFirst π.salt }

/-- the external position number x of table w, if there is one -/
def posX (w x : ℕ) : Option (Fin (2 ^ D.a) ⊕ Fin (2 ^ D.a)) :=
  if h : x < 2 ^ D.a then some (if w = 0 then .inl ⟨x, h⟩ else .inr ⟨x, h⟩) else none

/-- (d14), stored -/
def stoSwap (w x y : ℕ) (π : OneProtocolProof 256 (PSXE D dec).up) : OneProtocolProof 256 (PSXE D dec).up :=
  { π with ext := fun p =>
      if isAt (D := D) w x p then (posX (D := D) w y).bind π.ext
      else if isAt (D := D) w y p then (posX (D := D) w x).bind π.ext
      else π.ext p }

end S

end TypedOracleCompiler.Slice.Damage
