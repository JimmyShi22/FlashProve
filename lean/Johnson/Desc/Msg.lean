-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Msg.lean: THE ORACLES' STRINGS AT A BOUNDARY, READ AS COMMITTED MESSAGES; and the type
of witnesses. Definitions, and one small lemma (`pin_one`). It imports Johnson/Desc/Block.lean
alone.

Why. In the rule of composition (Johnson/Desc/Sound/ChainRule.lean, FileRule.lean) a statement at a
boundary is the carried record with the oracles: the stored table, and for every tree of the file
and every leaf a column of raw words. A relation at a boundary has to say of WHICH COMMITTED VALUES
it speaks, and to pin the witness to them. For that the strings want one reading, the same for all
kinds of block.

  `Strs`: the oracles at a boundary, as plain functions: `cell x`: the stored table's symbol at x
    (the position that it carries; its column); `col j x`: the column at leaf x of the tree number
    j. A tree's number is its number through the file, in the order of sending: the first chain's
    trees, then the shared chain's, then the second's. Empty where there is no such tree or leaf,
    and where the tree is not yet sent. (From the rule's own type of oracles: `strsOf`,
    Johnson/Desc/Sound/MsgAt.lean.)
  `Oracle.mainSkip`, `Oracle.maskSkip`, `Sym`, `Oracle.cut`: ONE TENANT's WORDS IN A COLUMN. By the
    format's rule on a leaf (R7.1, as OnBytes/Iop/Ground.lean's `TreeShape` cites it; the format's
    page not opened here) a column holds all tenants' main words, tenant by tenant
    in the order of sending, and behind them all tenants' mask words, likewise. Nothing where the
    column has not the words that the oracle message tells, or there is no such tenant.
  `FileDescription.oracleAt F j`: what the description's blocks tell of the tree number j where it is sent
    (`Block.oracles`).
  `wordOf F y j t`: **the committed word of tenant t of tree j**: leaf by leaf its main and its mask
    words: THE STRING, as it is, whether or not it is near a codeword.
  `Wit Cells Tok M`: **the type of witnesses**, one at all boundaries of all three chains: what the
    stored table commits to; the token heard; the messages, by number (main rows and mask rows);
    and, by seat, each copy's pad. Cells, Tok, M are letters.
  `far`, `Near`: SOME ENCODING of a message agrees with the committed word but for at most e leaves.
    enc: a letter: A RELATION: enc o j t m u: the word u (a symbol at each leaf) is an encoding of
    the message m as tenant t of tree j, of which o is told. NOT A FUNCTION OF THE MESSAGE: a code
    may encode with randomness of its own, which is no part of the message and which no sample
    reads. enc, rad and meets TAKE THE SEAT (j, t) BESIDE WHAT IS TOLD OF THE TREE: what is told
    holds neither the code nor the number of rows. AT THE RELEASE's RADIUS (Johnson's: at or past
    half the distance) SEVERAL MESSAGES CAN BE NEAR ONE WORD: so there is no function "the nearest
    message" here.
  `ListLe`: at most L messages are near any word: a form of a premise.
  `msgOf G w j t`: THE MESSAGE IS THE WITNESS's: the element of the list that the witness names.
    Which element it is has to be pinned by what each place supplies (a sample's answers; the
    record; earlier rounds): that is each boundary's relation's matter.
  `Reading`; `Member`, `NEAR`, `NearCode`, `PIN`, `NoColl`, `hasSmp`, `PINW`: the pinning by an
    out-of-domain sample, the promise beside it, and the stored table's decoding with its record:
    over eight letters that the library's own notions are to fill. There is no letter "decode" and
    none "clash": PIN says that the witness's message is a member of the list that meets the sample;
    NoColl that at most one member does. `pin_one` (proved): beside the promise the pinned message
    is fixed by the statement.
Limits. SILLY FILLINGS OF THE LETTERS, which the definitions do not shut out: enc := never: no
message is near any word, every PIN is false · enc := always (every word an encoding of every
message): the committed word itself serves: every message is near every shown word at every radius,
Member is `meets` alone, PIN says nothing of the committed word, NearCode is free · NOTHING ASKS
THAT A WORD ENCODES AT MOST ONE MESSAGE: at a filling without that, NoColl fails at an honest word
whenever both messages meet the sample · M := a message WITH its encoding's randomness: NoColl then
asks for one randomness too, which no sample gives · rad := 2 ^ n: every message is near every word
· meets := True: PIN is nearness alone, and NoColl says that the list has one member · smp :=
nothing: every PIN is false and every NoColl free (hence `hasSmp`) · arr := 0 everywhere: all
tenants name one message · lay := the first table everywhere: a message and its later copy, which
part at the pad, cannot both be pinned at one witness. THAT lay j t m m = m IS ASKED NOWHERE:
whoever lays both components of a witness to one table wants it (it holds at the filling that is
meant: the second table at the pad's places, the first elsewhere). Whoever fills the letters shows
them to be the code's. Words are raw (UInt64): that they are below the field's prime is the fold's
own test (`viewWordsBelowPrime`) on what is OPENED, not on a whole string. That a block cuts a column as
`Oracle.cut` does is each kind's matter (Block.lean's Limits, "TENANTS"). That `oracleAt`'s
log-length and words are the data's depth and width at that tree is not shown here (from `planOk`'s
last clause). That a tree which is sent passes unturned through the later blocks, and holds behind
its block what the prover's oracle holds, is not shown here (from the stage's text). Mask rows may
be shorter than the tree (R7.1: at x modulo their length): `enc` has to lay them so.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The oracles at a boundary, as plain functions. -/
structure Strs where
  /-- the stored table's symbol at x: the position that it carries, and its column -/
  cell : Nat → Option (Nat × List UInt64)
  /-- the column at leaf x of the tree number j -/
  col : Nat → Nat → List UInt64

/-- The words in front of tenant t's main words in a column. -/
def Oracle.mainSkip (o : Oracle) (t : Nat) : Nat := ((o.tenants.take t).map (·.main)).sum

/-- The words in front of tenant t's mask words in a column: all main words, then the earlier
tenants' mask words. -/
def Oracle.maskSkip (o : Oracle) (t : Nat) : Nat :=
  (o.tenants.map (·.main)).sum + ((o.tenants.take t).map (·.mask)).sum

/-- One tenant's words at one leaf. -/
structure Sym where
  main : List UInt64
  mask : List UInt64
  deriving DecidableEq, Repr, Inhabited

/-- **One tenant's words in a column.** -/
def Oracle.cut (o : Oracle) (t : Nat) (col : List UInt64) : Option Sym :=
  (o.tenants[t]?).bind fun n =>
    if col.length = o.words then
      some ⟨(col.drop (o.mainSkip t)).take n.main, (col.drop (o.maskSkip t)).take n.mask⟩
    else none

/-- What the description's blocks tell of the tree number j, through the file. -/
def FileDescription.oracleAt {Xi : Type} (F : FileDescription Xi) (j : Nat) : Option Oracle :=
  (oraclesOf F.first.blocksInOrder ++ oraclesOf F.shared.blocksInOrder ++ oraclesOf F.second.blocksInOrder)[j]?

/-- **The committed word of tenant t of tree j**, leaf by leaf. -/
def wordOf {Xi : Type} (F : FileDescription Xi) (y : Strs) (j t : Nat) : Nat → Option Sym :=
  fun x => (F.oracleAt j).bind fun o => o.cut t (y.col j x)

/-- **The type of witnesses.** -/
structure Wit (Cells Tok M : Type) where
  /-- what the stored table commits to -/
  cells : Cells
  /-- the token that was heard (the reply's block's extractor lays it; the asked token is the
  instance's) -/
  tok : Tok
  /-- the message number k, OUTSIDE ITS PAD's PLACES: one component for all copies of a message that
  is sent again (which tenant of which tree holds which message: `Reading.arr`) -/
  msg : Nat → M
  /-- tenant t of tree j: the table of which THE PAD's PLACES are read: A COMPONENT OF ITS OWN FOR
  EACH COPY, by its seat: a message that is sent again is sent with another pad -/
  pad : Nat → Nat → M

/-- At how many of the first 2 ^ n leaves a committed word parts from a word u. A leaf at which the
committed word shows nothing (the tree is not sent; the column has not its words) counts as parting.
-/
def far (n : Nat) (c u : Nat → Option Sym) : Nat :=
  ((List.range (2 ^ n)).filter fun x => (c x).isNone || c x != u x).length

/-- Some encoding of the message m agrees with the committed word of tenant t of tree j but for at
most e leaves; and the tree is told. -/
def Near {Xi M : Type} (F : FileDescription Xi) (enc : Oracle → Nat → Nat → M → (Nat → Option Sym) → Prop)
    (e j t : Nat) (y : Strs) (m : M) : Prop :=
  ∃ o u, F.oracleAt j = some o ∧ enc o j t m u ∧ far o.logLength (wordOf F y j t) u ≤ e

/-- A form of a premise: at most L messages are near any word. -/
def ListLe {Xi M : Type} (F : FileDescription Xi)
    (enc : Oracle → Nat → Nat → M → (Nat → Option Sym) → Prop) (e L : Nat) : Prop :=
  ∀ (y : Strs) (j t : Nat) (l : List M), l.Nodup → (∀ m ∈ l, Near F enc e j t y m) → l.length ≤ L

/-! ## The pinning by a sample, and the stored table -/

/-- **The letters of the reading**, in one record: what a code, a sample and the stored table's
record give. A: the chain's whole record at a boundary, WITH WHAT WAS HANDED TO THE CHAIN (the
public part holds the stored table's record). Smp: a sample's seed with its answers. Rec: the stored
table's record. None of the fields is filled here: they are letters for the library's own notions.
-/
structure Reading (A Cells M Smp Rec : Type) where
  /-- which message tenant t of tree j holds: its number in the witness. A message that is kept and
  sent again has one number -/
  arr : Nat → Nat → Nat
  /-- tenant t of tree j: the table that is the first one outside the tenant's pad's places and the
  second one at them -/
  lay : Nat → Nat → M → M → M
  /-- the encodings: enc o j t m u: the word u (the symbol at each leaf) is an encoding of the
  message m as tenant t of tree j, of which o is told: a relation: a code may encode with a
  randomness of its own -/
  enc : Oracle → Nat → Nat → M → (Nat → Option Sym) → Prop
  /-- the radius, in leaves, at which the sending kind promises and the closing kind tests -/
  rad : Oracle → Nat → Nat → Nat
  /-- the message's answers at the sample's seed are the sample's answers -/
  meets : Oracle → Nat → Nat → M → Smp → Prop
  /-- the sample of tenant t of tree j, off the record: nothing where it has none (yet, or any more)
  -/
  smp : A → Nat → Nat → Option Smp
  /-- what the stored table decodes to, with its record -/
  decT : (Nat → Option (Nat × List UInt64)) → Rec → Option Cells
  /-- the stored table's record, off the chain's record -/
  recOf : A → Option Rec

section
variable {Xi A Cells Tok M Smp Rec : Type} (F : FileDescription Xi) (G : Reading A Cells M Smp Rec)

/-- **The message of tenant t of tree j**: the one that the witness names: outside the pad's places
by the message's number, at them by the seat. -/
def msgOf (w : Wit Cells Tok M) (j t : Nat) : M := G.lay j t (w.msg (G.arr j t)) (w.pad j t)

/-- A member of the list of tenant t of tree j that meets the sample z: an encoding of it is near
the committed word, at the radius, and it answers the sample's seed as the sample says. -/
def Member (o : Oracle) (j t : Nat) (y : Strs) (z : Smp) (m : M) : Prop :=
  (∃ u, G.enc o j t m u ∧ far o.logLength (wordOf F y j t) u ≤ G.rad o j t) ∧ G.meets o j t m z

/-- **NEAR (j, t)**: for a tenant without a sample (a fresh mask): the tree is told, and the
witness's message is near the committed word, at the radius. IT DOES NOT FIX THE MESSAGE: it is one
of a list. -/
def NEAR (j t : Nat) (y : Strs) (w : Wit Cells Tok M) : Prop :=
  ∃ o u, F.oracleAt j = some o ∧ G.enc o j t (msgOf G w j t) u ∧
    far o.logLength (wordOf F y j t) u ≤ G.rad o j t

/-- **NearCode (j, t)**: the committed word is near the code: SOME message is near it, at the
radius. It reads no component of the witness. -/
def NearCode (j t : Nat) (y : Strs) : Prop :=
  ∃ o m u, F.oracleAt j = some o ∧ G.enc o j t m u ∧
    far o.logLength (wordOf F y j t) u ≤ G.rad o j t

/-- **PIN (j, t)**: the tree is told, the record holds the tenant's sample, and the witness's
message is a member of the committed word's list that meets it. -/
def PIN (j t : Nat) (a : A) (y : Strs) (w : Wit Cells Tok M) : Prop :=
  ∃ o z, F.oracleAt j = some o ∧ G.smp a j t = some z ∧ Member F G o j t y z (msgOf G w j t)

/-- **NoColl (j, t)**: the promise: at most one member of the committed word's list meets the
sample. So beside it PIN fixes the witness's message by the statement alone. IT IS FREE WHERE THE
RECORD HOLDS NO SAMPLE: that the record holds one is a test on the record (`hasSmp`), to be promised
beside it. -/
def NoColl (j t : Nat) (a : A) (y : Strs) : Prop :=
  ∀ o z, F.oracleAt j = some o → G.smp a j t = some z →
    ∀ m m', Member F G o j t y z m → Member F G o j t y z m' → m = m'

/-- The record holds the sample of tenant t of tree j: a test with code wherever `smp` has code. -/
def hasSmp (j t : Nat) (a : A) : Bool := (G.smp a j t).isSome

/-- **PINW**: the witness's cells are what the stored table decodes to, with the record. -/
def PINW (a : A) (y : Strs) (w : Wit Cells Tok M) : Prop :=
  ∃ r, G.recOf a = some r ∧ G.decT y.cell r = some w.cells

/-- Beside the promise a pinned message is one: two witnesses that are both pinned name the same. -/
theorem pin_one (j t : Nat) (a : A) (y : Strs) (w w' : Wit Cells Tok M) (h : NoColl F G j t a y)
    (p : PIN F G j t a y w) (p' : PIN F G j t a y w') : msgOf G w j t = msgOf G w' j t := by
  obtain ⟨o, z, ho, hz, hm⟩ := p
  obtain ⟨o', z', ho', hz', hm'⟩ := p'
  have e1 : o' = o := Option.some.inj (ho'.symm.trans ho)
  have e2 : z' = z := Option.some.inj (hz'.symm.trans hz)
  subst e1
  subst e2
  exact h o' z' ho hz _ _ hm hm'

end

end VerifiableInference.Desc
