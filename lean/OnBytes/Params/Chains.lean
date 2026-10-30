-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Chains.lean: the seven chains of a key, an entry and a proof: what enters the
first hash call of each, and its description for the strict reader.

A key file has three chains (one-time, shared, second), an entry file one (the link's) and a proof
file three (first, shared, second). Each of the seven has a label of its own. The format page
(docs/format/FORMAT.md) fixes for each its label, the names and the order of its parameter items,
the items of its statement, and where its 32 random bytes come from (that page's rules R13.4 to
R13.6, R14.3, R14.9, R14.10; every number of this kind below is a rule of that page). The C++
counterparts are `bind_one_time_chain` (blocks/frame/check_key.h), `bind_request_parameters`,
`bind_request_statement`, `bind_shared_chain` and `bind_second_chain` (blocks/frame/check.h), and
the binding routines of blocks/iop/lin.h and blocks/iop/link.h.

For each chain this file has
 - a record of what its parameter bytes hold, and a reader that refuses other names or another
   order of the items. One exception: after its own seven items a proof's first chain may hold
   further items under any names, those of the caller's sub-proofs; they are handed on unread.
   `configure` (OnBytes/Params/Configure.lean) writes none;
 - the bytes of its statement, from the roots, answers, seals and request that the caller has;
 - its description. The rounds come from the protocol's blocks.
It also has the tests that tie the parameter bytes of the chains of one file to each other.

Main definitions: `OneTime`, `Shared`, `Second`, `Link`, `First`, with `read`, `statement` and
`describe` for each; `KeyChains`, `ProofChains`.
-/
import OnBytes.Params.Given
import OnBytes.Params.Items

namespace OnBytes.Params

/-! ## Labels and names -/

/-- The label of a proof's first chain. -/
def labelFirst : Nat := 0x46524d01
/-- The label of a key's one-time chain. -/
def labelOneTime : Nat := 0x46524d02
/-- The label of a key's shared chain. -/
def labelShared : Nat := 0x4c494e01
/-- The label of a key's second chain. -/
def labelSecond : Nat := 0x4c494e02
/-- The label of a proof's shared chain (R14.9). -/
def labelSharedProof : Nat := 0x46524d03
/-- The label of a proof's second chain (R14.10). -/
def labelSecondProof : Nat := 0x46524d04
/-- The label of the link's chain of an entry. -/
def labelLink : Nat := 0x4c4e4b01

/-- A stored table as a statement names it: its root and the answers of its record, by row and
within a row by answer. It is an item of the statement
and no parameter: root and answers come out of a key file or an entry file, and such a file never
sets a parameter (R0.2). -/
structure TableName where
  root : ByteArray
  answers : List E := []

/-- The rounds of a chain as the protocol's blocks state them, each with the stored trees that it
opens. -/
abbrev Rounds : Type := List (Fmt.Round × List Fmt.Stored)

/-- The description of a chain from its parameter bytes, label, statement, random bytes and
rounds. -/
def describeWith (g : Given) (label : Nat) (statement : ByteArray) (rand : Fmt.Rand) (r : Rounds)
    (firstTree : Nat := 0) : Option Fmt.SpecX :=
  g.describe label statement rand (r.map (·.1)) (r.map (·.2)) firstTree

/-! ## A key's one-time chain -/

/-- What the parameter bytes of a key's one-time chain hold. `indexMasks` is the notice of the
index-mask message, an oracle message of mask rows only with which the chain begins. -/
structure OneTime where
  given : Given
  indexMasks : OracleNotice
  ranges : WfPublic
  binding : LinBindingShape
  codes : Codes
  lin : LinShape

/-- Reads the parameter bytes of a key's one-time chain. -/
def OneTime.read (b : ByteArray) : Option OneTime := do
  let g ← Given.read b
  match g.items with
  | [("index-mask message", m), ("ranges", r), ("binding tree", t), ("codes", c),
     ("the test on the table", l)] =>
    pure ⟨g, ← readNotice m, ← readRanges r, ← readBinding t, ← readCodes c, ← readLin l⟩
  | _ => none

/-- The statement of a key's one-time chain: the first table. -/
def OneTime.statement (table : TableName) : ByteArray :=
  Fmt.tableItem "table" table.root (table.answers.map E.triple)

/-- The description of a key's one-time chain. Its random bytes are in the file. -/
def OneTime.describe (p : OneTime) (table : TableName) (r : Rounds) : Option Fmt.SpecX :=
  describeWith p.given labelOneTime (OneTime.statement table) .inFile r

/-! ## A shared chain -/

/-- What the parameter bytes of a shared chain hold. -/
structure Shared where
  given : Given
  codes : Codes
  lin : LinShape

/-- Reads the parameter bytes of a shared chain. -/
def Shared.read (b : ByteArray) : Option Shared := do
  let g ← Given.read b
  match g.items with
  | [("codes", c), ("the test on the table", l)] => pure ⟨g, ← readCodes c, ← readLin l⟩
  | _ => none

/-- The statement of a shared chain: the table, and the root of the binding tree. That is the
salted tree whose leaves are the seals of the first chains of a batch's requests; in a key it has
one leaf, the seal of the one-time chain (R13.6, R14.7). -/
def Shared.statement (table : TableName) (bindingRoot : ByteArray) : ByteArray :=
  Fmt.tableItem "table" table.root (table.answers.map E.triple) ++
    Fmt.item Fmt.bindRootName bindingRoot

/-- The description of a shared chain under a label: `labelShared` in a key, `labelSharedProof` in a
proof. The root of the binding tree takes the place of its random bytes, and the file holds no
random bytes for it. -/
def Shared.describe (p : Shared) (label : Nat) (table : TableName) (bindingRoot : ByteArray)
    (r : Rounds) : Option Fmt.SpecX :=
  describeWith p.given label (Shared.statement table bindingRoot) (.given bindingRoot) r

/-! ## A second chain -/

/-- What the parameter bytes of a second chain hold: no item after the digest of the public
files. -/
structure Second where
  given : Given

/-- Reads the parameter bytes of a second chain. -/
def Second.read (b : ByteArray) : Option Second := do
  let g ← Given.read b
  if g.items.isEmpty then pure ⟨g⟩ else none

/-- The statement of a second chain: the seal of the chain with which the file begins (a key's
one-time chain, a proof's first chain), then the seal of the file's shared chain. A seal is the
digest in which a chain ends and on which later chains build. -/
def Second.statement (own shared : ByteArray) : ByteArray := Fmt.sealItems [own, shared]

/-- The description of a second chain under a label: `labelSecond` in a key, `labelSecondProof` in a
proof. Its random bytes are in the file. `firstTree` is the number of the first tree that it sends
itself: its own trees are numbered after the trees that it takes over from the file's earlier
chains. -/
def Second.describe (p : Second) (label : Nat) (own shared : ByteArray) (r : Rounds)
    (firstTree : Nat) : Option Fmt.SpecX :=
  describeWith p.given label (Second.statement own shared) .inFile r firstTree

/-! ## The link's chain of an entry -/

/-- What the parameter bytes of a link's chain hold. -/
structure Link where
  given : Given
  codes : Codes
  link : LinkShape

/-- Reads the parameter bytes of a link's chain. -/
def Link.read (b : ByteArray) : Option Link := do
  let g ← Given.read b
  match g.items with
  | [("codes", c), ("the link", l)] => pure ⟨g, ← readCodes c, ← readLink l⟩
  | _ => none

/-- The statement of a link's chain: the first table, then the further table. -/
def Link.statement (first further : TableName) : ByteArray :=
  Fmt.tableItem "the first table" first.root (first.answers.map E.triple) ++
    Fmt.tableItem "the further table" further.root (further.answers.map E.triple)

/-- The description of a link's chain. Its random bytes are in the file. -/
def Link.describe (p : Link) (first further : TableName) (r : Rounds) : Option Fmt.SpecX :=
  describeWith p.given labelLink (Link.statement first further) .inFile r

/-! ## A proof's first chain -/

/-- What the parameter bytes of a proof's first chain hold. -/
structure First where
  given : Given
  codes : Codes
  lin : LinShape
  shape : ReqShape
  layout : ReqLayout
  /-- one number for each link -/
  identifiers : List Nat
  /-- how many linear claims on the table's matrix ("rows") the links' sub-proofs leave to the
  test on the table -/
  pendingRows : Nat
  binding : LinBindingShape
  /-- the items that the caller's sub-proofs take as data, after the seven above. The format page
  does not rule them, and nothing here reads their names or values -/
  more : List (String × ByteArray)

/-- Reads the parameter bytes of a proof's first chain. Refused, since they are no items of a
proof (R14.3): a shape whose list `atStart` does not hold exactly one notice; links whose numbers
of plain scalars are not 0, .., 0, 1; identifiers or a layout without exactly one entry for each
link; `pendingRows` = 0; and a plan with an entry for a table's own sample. -/
def First.read (b : ByteArray) : Option First := do
  let g ← Given.read b
  match g.items with
  | ("codes", c) :: ("the test on the table", l) :: ("request's shape", s) :: ("layout", y) ::
      ("links' identifiers", i) :: ("pending rows", n) :: ("binding tree", t) :: more =>
    let p : First := ⟨g, ← readCodes c, ← readLin l, ← readReq s, ← readLayout y, ← readWords i,
      ← readWord n, ← readBinding t, more⟩
    let links := p.shape.link.length
    if p.shape.atStart.length == 1 &&
        p.shape.link.map (·.plain) == List.replicate (links - 1) 0 ++ [1] &&
        p.identifiers.length == links && p.layout.link.length == links &&
        decide (1 ≤ p.pendingRows) && g.record.isNone then pure p
    else none
  | _ => none

/-- The statement of a proof's first chain (R14.3), four items: the stored copy on which the proof
was made; the number under which that copy is kept; the request as one string of bytes, as the
caller passes it in; and `words`, the caller's request itself, byte for byte. For a model's proof
`request` holds the request file only as a digest (OnBytes/Proof/RequestItem.lean), and `words` is
the request file, whole. The reply is no item: it is sent unmasked in a round of its own, REPLY
(R14.8). -/
def First.statement (table : TableName) (copy : Nat) (request words : ByteArray) : ByteArray :=
  Fmt.tableItem "table" table.root (table.answers.map E.triple) ++
    Fmt.item "stored copy" (Fmt.u64n copy) ++ Fmt.item "request" (Fmt.text request) ++
    Fmt.item "the request file's words" (Fmt.text words)

/-- The description of a proof's first chain. Its random bytes are in the file. -/
def First.describe (p : First) (table : TableName) (copy : Nat) (request words : ByteArray)
    (r : Rounds) : Option Fmt.SpecX :=
  describeWith p.given labelFirst (First.statement table copy request words) .inFile r

/-! ## The chains of one file together -/

/-- True if two chains have the same settings in their plans and the same digest of the public
files. -/
def sameSetting (a b : Given) : Bool :=
  a.plan.field == b.plan.field && a.plan.salt == b.plan.salt && a.plan.nonce == b.plan.nonce &&
    a.plan.posB == b.plan.posB && a.plan.samples == b.plan.samples &&
    a.plan.saved == b.plan.saved && a.cfg == b.cfg

/-- True if an item has the same bytes in two chains. -/
def sameItem (a b : Given) (name : String) : Bool :=
  match a.item name, b.item name with
  | some x, some y => x == y
  | _, _ => false

/-- The three chains of a key. -/
structure KeyChains where
  oneTime : OneTime
  shared : Shared
  second : Second

/-- Reads the parameter bytes of a key's three chains. Refused: chains under different settings
or public files; items "codes" or "the test on the table" that differ between the one-time chain
and the shared chain; and a shared or second chain whose plan has an entry for a table's own
sample (R13.15). -/
def KeyChains.read (oneTime shared second : ByteArray) : Option KeyChains := do
  let a ← OneTime.read oneTime
  let b ← Shared.read shared
  let c ← Second.read second
  if sameSetting a.given b.given && sameSetting a.given c.given &&
      sameItem a.given b.given "codes" && sameItem a.given b.given "the test on the table" &&
      b.given.record.isNone && c.given.record.isNone then pure ⟨a, b, c⟩
  else none

/-- The three chains of a proof. -/
structure ProofChains where
  first : First
  shared : Shared
  second : Second

/-- Reads the parameter bytes of a proof's three chains. Refused: chains under different settings
or public files; items "codes" or "the test on the table" that differ between the first chain and
the shared chain (R14.9); and a shared or second chain whose plan has an entry for a table's own
sample (`First.read` refuses such a plan of the first chain). -/
def ProofChains.read (first shared second : ByteArray) : Option ProofChains := do
  let a ← First.read first
  let b ← Shared.read shared
  let c ← Second.read second
  if sameSetting a.given b.given && sameSetting a.given c.given &&
      sameItem a.given b.given "codes" && sameItem a.given b.given "the test on the table" &&
      b.given.record.isNone && c.given.record.isNone then pure ⟨a, b, c⟩
  else none

end OnBytes.Params
