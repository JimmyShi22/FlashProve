-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8.lean: a chain in a file: the strict reader, as one fold over the chain's rounds, with the
chain's value in its state.

This file is about the verifier's parser for a non-interactive proof: it reads a chain's bytes round
by round while it recomputes the hash chain (`Chain`, Fmt/Rules5.lean) from which the verifier's
messages are drawn, and it checks proof of work and Merkle openings on the way. The plan (`Plan`,
Fmt/Plan.lean) has the field, some lengths, and for each round an entry with its message's size, its
work and its draws.
A proof file of the programs (the C++ implementation that comes with this Lean code) holds a chain's
bytes: its items in the order of the protocol, without lengths, names or separators. No value of the
chain and no block of an answer stands in the file. So the file cannot be cut into items first and
hashed afterwards: how many bytes an opening has depends on the drawn positions, these on the
round's answer, that on the chain's value. Reading and hashing are one pass. Every function is
total; whatever test on the file's bytes fails ends in "refused" (none). This reader is what other
heads call the strict reader: this library's rendering of the format page's verifier up to its
decision.

Generic in the hash, through a monad. The first argument h (number, tree, index, start, bytes)
answers in a monad m. At m := Id and the format's own hash this file is a program that can be
evaluated (the tests); at a monad of query trees the same text is a verifier's parser that asks the
oracle.

Sources. Section 8 of the format page (docs/format/FORMAT.md, which comes with the programs): R8.1
to R8.10, as far as this file renders them. This file is not held against the page as it
ships, and may differ from it. R8.7: the trees of one list are opened by increasing place in the
reading chain's list (R7.13); for a chain's own trees that is the order of their numbers, which
`Round.ok` asks; for trees that are taken over see "Not tested" below.
No Mathlib.
   R7.14, as this file reads it. The record of met vertices is keyed by the
   root's 32 bytes, within a session:
   one record for every root that is read, whichever tree, chain or file it came with. So two trees
   that are sent with one root share a record, and so do a tree and the later chain that takes it
   over, and a stored table and all chains that read it. Within a record a value is keyed by depth
   and place. The root's own value is not entered (Fmt/Rules7.lean's `entered`). Only what an
   accepted opening shows is entered: `addSeen` stands behind the test of the walk's end against the
   root. (The span is the page's own word, as this file reads it:
   R0.5 and section 9.)
   The session. By the page: one run of a verifier that ends in one verdict: all chains of a file,
   and all files that one verdict reads. Here: `readChain` takes a record and gives it back
   (`ChainOut.seen`), so that whoever reads several chains for one verdict can hand it on;
   `wholeChain` starts from the empty record: a session of one chain. A verdict on several chains or
   files is not rendered in this file.
   R2.7 (as this file reads it) is a clause of `Spec.ok`, the first
   (`Spec.small`): parameters, a statement, a round's message or a leaf's bytes that would make a
   hashed string longer than the hash admits are no plan, statement, file or shape of the format,
   and a verifier refuses. All these lengths follow from the description, which is public; so the
   test looks at no file.

Where each rule stands. R8.1: `readChain` (items in the order of the protocol, no lengths; refused
if the file ends too early), `wholeChain`. R8.2: `Item`, `readItems` (what enters a query),
`readNonce` (the nonce enters the query as a word of its own, not as an item of the message),
`readList`, `readOpens` (what does not). R8.3, R8.4, R8.5, R8.6, R8.10 and R8.7's order of a chain's
own trees: conditions of `Round.ok`, with R5.3, R4.5 (c), R7.13 (an own tree's number is the number
of the chain's first tree plus its place in the order of sending); that the count stays below 2^16
is a clause of `Spec.ok`. R8.7: `step`. R8.8: `Item`, `Round.items` (the cut of a message into items
belongs to each protocol: the reader is told). R8.9: `readChain` reads from a place and gives the
place behind, so that a file can hold several chains. R4.3: `Spec.ok`'s second clause (`ok_params`
in Fmt/Rules8Ok.lean). R6.2's last sentence: a clause of `Spec.ok`, by `Entry.fits` of
Fmt/Rules6Round.lean. R4.5: `Rand`. R5.1: a chain can end with a round of any kind: no clause.
R7.15: `readOpens` (a tree of depth a under a draw below 2^k is opened at the set of the short
positions). R7.14: `agree`, `addSeen`. R0.3: a refusal is the value none, never a stop: every
function is total.

1. What the file contains.
   What the reader must be told beside the plan. The page says that every length follows from the
   plan, the shapes and the drawn positions. That is so; but a reader also refuses (an element's
   eight bytes that are not below the prime; an opening that does not end in its root), and for that
   it must know more than the plan's entry holds. This is why a description (`Spec`) has more than
   the plan:
    `Item`: How a round's message is cut: an element of the base field, of the extension field, a
      word, a root, an answer to an out-of-domain sample.
    `Src`: Where the root and the start of an opened tree come from: the n-th root sent on this
      chain (its start is the chain's run's value), or a root and a start given from outside (a
      stored tree; a tree of an earlier chain).
    `Round`: An entry of the plan, its kind, its message's items, and the trees that are opened
      behind its draw of positions, in the order of the protocol.
    `Rand`: The three cases of a chain's random bytes: the first 32 bytes of the chain in its file;
      given; none.
    `Spec`: The description: a chain as a reader needs it: label, plan, the parameter bytes, the
      statement's bytes, the case of the random bytes, the number of its first tree, the
      configuration's digest (R4.9: an item of the parameters and the start of every vertex), its
      rounds.
    `Spec.shapeOf`: A tree's shape stands where the tree is opened, not where its root is sent.
    `Spec.ok`: The conditions on these data that do not look at a file: the parameter bytes begin
      with the version's item, this very plan's bytes and this configuration's item (R4.3); the
      rounds are the plan's entries (the one under the name RECORD passed over: `recordName`,
      Fmt/Rules4.lean); each message's items have the entry's bytes, roots and answers; the page's
      rules on the order of items; a tree of the chain's own that is opened more than once has one
      shape; no tree is deeper than 48 (R7.16); the salts' length is one that the format admits
      (R7.3); and more. (The whole list stands at the definition; each clause under a name:
      Fmt/Rules8Ok.lean.)
   The reader.
    `readItems`: A message's items, each by its own rule.
    `readNonce`: The low bytes of a nonce, lowest first.
    `readList`: The listed positions, compared with the list that was derived.
    `agree`, `addSeen`: One value at a vertex under one root: a root can be read at several lists,
      in several rounds, by several chains of a session, and with several trees; the reader keeps,
      for each root's 32 bytes, the vertices that it has met under it, computed or given, but for
      the root itself, and refuses if one gets a second value.
    `step`: One round: message; nonce; the round's query (a fixed number of blocks, by the plan's
      entry and the round's kind) with the test of work; the draws; the list; the openings, each
      checked against its root and against what was met under that root before.
    `readChain`: The random bytes and the first value; then the fold; gives what was read and the
      place behind the chain.
    `wholeChain`: The same, and refuses a file with a byte behind the chain.

2. What is checked when the file compiles. 39 tests (#guard). The page's known answer of this
section (a whole chain in a file, with a tree and an opening, in both fields). And, of this
library's own: the example chain of the sections on the first query, on a round's query and on
drawing, put into a file and read back to those sections' known answers; altered copies of both.

3. Theorems. None in this file.

4. What is this library's own, what is not tested, what is not claimed.
   This library's own, not the page's (it is silent): data that do not meet `Spec.ok` are refused
   whatever the file; a chain without a round is not in order.
   Not tested of R8.7: where, among a round's openings, the trees stand that a chain has taken over
   from other chains (`Src.given` does not say from which chain a tree comes): the reader follows
   `Round.opens`. Nor that stored trees are opened first (R8.7, as this file reads it):
   that order is
   rendered in Fmt/Rules8X.lean, for rounds that open stored trees alone (see its part 4).
   Not tested: R8.3's "all answers that the seeds ask for": the number of answers is a word of the
   entry; that it is what the seeds ask for is, by the page, a condition on plans (how many oracle
   messages are sampled is not in the plan).
   Not claimed: which `Spec` belongs to which protocol; what a verifier does with what was read.
-/
import Fmt.Plan
import Fmt.Rules4
import Fmt.Rules5
import Fmt.Rules6Round
import Fmt.Rules7

namespace Fmt

/-! ## What a reader is told -/

/-- An item of a prover's message that enters the round's query. -/
inductive Item where
  | f
  | e
  | word
  | root
  | answer
  deriving DecidableEq, Repr, Inhabited

def Item.bytes : Item → Nat
  | .f => 8
  | .e => 24
  | .word => 8
  | .root => 32
  | .answer => 24

/-- An item as read. -/
inductive ItemValue where
  | f (x : UInt64)
  | e (x : UInt64 × UInt64 × UInt64)
  | word (x : UInt64)
  | root (d : ByteArray)
  | answer (x : UInt64 × UInt64 × UInt64)
  deriving DecidableEq, Inhabited

/-- Where the root and the start of an opened tree come from. -/
inductive Src where
  | own (n : Nat)
  | given (root start : ByteArray)
  deriving DecidableEq, Inhabited

/-- A round, as a reader needs it. -/
structure Round where
  entry : Entry
  kind  : Kind
  items : List Item := []
  opens : List (Shape × Src) := []
  deriving DecidableEq

/-- The three cases of a chain's random bytes. -/
inductive Rand where
  | inFile
  | given (b : ByteArray)
  | none

/-- A chain, as a reader needs it. -/
structure Spec where
  label     : Nat
  plan      : Plan
  params    : ByteArray
  statement : ByteArray
  rand      : Rand
  firstTree : Nat := 0
  /-- The configuration's digest (R4.9): the first item behind the plan in the parameters, and the
  start of every vertex of every tree (R7.7). -/
  cfg       : ByteArray
  rounds    : List Round

def countItem (i : Item) (l : List Item) : Nat := (l.filter (· == i)).length

/-- Each number is above the one before it. -/
def increasing : List Nat → Bool
  | a :: b :: l => a < b && increasing (b :: l)
  | _ => true

/-- The conditions on one round; "after" says whether the round before it was one of seeds; "sent"
is the number of roots sent before it. -/
def Round.ok (P : Plan) (noRand : Bool) (firstTree : Nat) (after : Bool) (sent : Nat) (r : Round) :
    Bool :=
  -- the message: bytes, roots, answers as the entry says; a multiple of eight bytes
  (r.items.map Item.bytes).sum == r.entry.msg && countItem .root r.items == r.entry.roots &&
    countItem .answer r.items == r.entry.answers &&
  r.entry.count == 1 && r.entry.work ≤ 64 &&
  -- R5.3: no work before an empty message of the verifier, nor before a seal
  ((r.kind != .nothing && r.kind != .sealed) || r.entry.work == 0) &&
  -- R8.2: a nonce in a file has one to eight bytes, also where no round has work
  1 ≤ P.nonce && P.nonce ≤ 8 &&
  -- answers stand at the head of the message behind a round of seeds, and nowhere else
  (r.items.take r.entry.answers).all (· == .answer) && (after || r.entry.answers == 0) &&
  -- in a round that joins a hiding polynomial its sum is the last item
  (r.kind != .join || r.items.getLast? == some .e) &&
  -- R8.5: a root stands in a round of kind 1 to 5: not before an empty message of the verifier, not
  -- before a seal; R4.5 (c): a chain without random bytes sends none
  (r.entry.roots == 0 || (r.kind != .nothing && r.kind != .sealed && !noRand)) &&
  -- positions below 2 ^ logN, logN below 64; a listed position can be spelled
  r.entry.logN < 64 && (r.entry.poss == 0 || P.posB == 0 || r.entry.logN ≤ 8 * P.posB) &&
  -- openings stand behind a draw of positions; an own tree's root has been sent, and its number is
  -- firstTree plus its place in the order of sending
  (r.opens.isEmpty || 0 < r.entry.poss) &&
  -- R8.7: a chain's own trees are opened in the order of their numbers
  increasing (r.opens.filterMap fun o => match o.2 with
    | .own n => some n
    | .given _ _ => none) &&
  r.opens.all fun o => o.1.a ≤ r.entry.logN && (match o.2 with
    | .own n => n < sent + r.entry.roots && o.1.tree == firstTree + n && !o.1.stored && !noRand
    | .given root start => root.size == 32 && start.size == 32)

def roundsOk (P : Plan) (noRand : Bool) (firstTree : Nat) : Bool → Nat → List Round → Bool
  | _, _, [] => true
  | after, sent, r :: rs =>
    r.ok P noRand firstTree after sent &&
      roundsOk P noRand firstTree (r.kind == .seeds) (sent + r.entry.roots) rs

def Rand.isNone : Rand → Bool
  | .none => true
  | _ => false

/-- The chain's own trees that are opened somewhere, by their places in the order of sending, each
with the shape under which it is opened. -/
def Spec.ownShapes (S : Spec) : List (Nat × Shape) :=
  S.rounds.flatMap fun r => r.opens.filterMap fun o => match o.2 with
    | .own n => some (n, o.1)
    | .given _ _ => none

/-- The shape of the n-th tree whose root is sent on this chain; none if no round opens it. -/
def Spec.shapeOf (S : Spec) (n : Nat) : Option Shape := (S.ownShapes.find? (·.1 == n)).map (·.2)

/-- R2.7, R2.3: nothing that is hashed is longer than the hash admits: the parameters' bytes; what
is hashed for the first value (the statement and 88 bytes more); every round's message with the 16
bytes behind it; every opened leaf (a column of at least one word and fewer than 2 ^ 24: R2.3; the
salt's length: `Spec.ok`'s last clause); and a chain has fewer than 2 ^ 63 rounds. All of it is
public: data beyond these bounds are no plan, statement or shape of the format. -/
def Spec.small (S : Spec) : Bool :=
  decide (S.params.size ≤ 2 ^ 32 - 144) && decide (S.statement.size + 88 ≤ 2 ^ 32 - 144) &&
    (S.rounds.all fun r => decide (r.entry.msg + 16 ≤ 2 ^ 32 - 144)) &&
  (S.rounds.all fun r => r.opens.all fun o => decide (1 ≤ o.1.W) && decide (o.1.W < 2 ^ 24)) &&
    decide (S.rounds.length < 2 ^ 63)

/-- The conditions that do not look at a file. -/
def Spec.ok (S : Spec) : Bool :=
  -- R2.7: within the hash's bounds
  S.small &&
  -- R4.3: the parameters' bytes begin with the format's version, this plan and this configuration's
  -- digest: so the chain's first value is a hash of the version, the plan and the configuration's
  -- digest that the reader follows
  S.params.extract 0 (paramsBytes S.plan S.cfg []).size == paramsBytes S.plan S.cfg [] &&
  S.plan.ok && S.rounds.map (·.entry) == S.plan.rounds &&
  -- R6.2: an entry has its kind's draws and no others
  (S.rounds.all fun r => r.entry.fits r.kind S.plan.samples) &&
  (match S.rand with
    | .given b => b.size == 32
    | _ => true) &&
  S.cfg.size == 32 &&
  -- this library's own: a chain has a round
  !S.rounds.isEmpty &&
  -- R7.13: the count of the trees does not reach 2 ^ 16; a tree that is taken over has a number
  -- below it too
  S.firstTree + ((S.rounds.map (·.entry.roots)).sum) < 2 ^ 16 &&
    (S.rounds.all fun r => r.opens.all fun o => o.1.tree < 2 ^ 16) &&
  -- a tree of the chain's own that is opened more than once has one shape
  (S.ownShapes.all fun x => S.shapeOf x.1 == some x.2) &&
  roundsOk S.plan S.rand.isNone S.firstTree false 0 S.rounds &&
  -- R7.16: no tree is deeper than 48
  (S.rounds.all fun r => r.opens.all fun o => depthOK o.1.a) &&
  -- R7.3: the length of a leaf's salt is a word of the plan, which is public: a plan with another
  -- length than the format admits is no plan of the format, also where no round has an opening (the
  -- page as this library reads it): refused here, whatever the file
  saltLenOK S.plan.salt

/-! ## What was read -/

/-- One round as read. -/
structure RoundOut where
  msg   : ByteArray
  vals  : List ItemValue
  nonce : Nat
  drawn : Drawn
  list  : List Nat
  /-- For each opening: the tree's shape, the list at which it was opened, what was read. -/
  opens : List (Shape × List Nat × OpenOut)

/-- For each root read, under its 32 bytes: the vertices met, as (depth, place, value). -/
abbrev Seen : Type := List (ByteArray × List (Nat × Nat × ByteArray))

/-- The fold's state: the place in the file, the chain between rounds, the roots sent so far, the
vertices met under each root, what was read. -/
structure St where
  pos   : Nat
  chain : Chain
  roots : Array ByteArray
  seen  : Seen
  out   : Array RoundOut

/-- A chain as read. -/
structure ChainOut where
  pd     : ByteArray
  run    : Option ByteArray
  rho0   : ByteArray
  rho    : ByteArray
  seen   : Seen
  rounds : Array RoundOut

/-! ## The readers that do not hash -/

def readItem (f : Fld) : Item → Rd ItemValue
  | .f => fun b i => (rdElt f b i).map fun x => (.f x.1, x.2)
  | .e => fun b i => (rdExt f b i).map fun x => (.e x.1, x.2)
  | .word => fun b i => (rdWord b i).map fun x => (.word x.1, x.2)
  | .root => fun b i => (rdDigest b i).map fun x => (.root x.1, x.2)
  | .answer => fun b i => (rdExt f b i).map fun x => (.answer x.1, x.2)

def readItems (f : Fld) : List Item → Rd (List ItemValue)
  | [] => fun _ i => some ([], i)
  | t :: ts => fun b i =>
    match readItem f t b i with
    | some (x, j) =>
      match readItems f ts b j with
      | some (l, k) => some (x :: l, k)
      | none => none
    | none => none

/-- n bytes as a number, the lowest first. -/
def leNat (b : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (byteAt b i).toNat + 256 * leNat b (i + 1) n

def readLE (n : Nat) : Rd Nat := fun b i =>
  if i + n ≤ b.size then some (leNat b i n, i + n) else none

/-- The nonce of a round: no byte where there is no work. -/
def readNonce (P : Plan) (w : Nat) : Rd Nat :=
  if w == 0 then fun _ i => some (0, i) else readLE P.nonce

/-- The listed positions: compared with the list that was derived. -/
def readList (P : Plan) (poss : Nat) (l : List Nat) : Rd Unit := fun b i =>
  if P.posB == 0 || poss == 0 then some ((), i)
  else
    match rdMany (readLE P.posB) l.length b i with
    | some (l', j) => if l' == l then some ((), j) else none
    | none => none

/-- No vertex has one value in the one list and another in the other. -/
def agree (old new : List (Nat × Nat × ByteArray)) : Bool :=
  new.all fun v => old.all fun o => !(o.1 == v.1 && o.2.1 == v.2.1) || o.2.2 == v.2.2

/-- R7.14: one value at a vertex under one root: the vertices of a further opening are laid to those
met under that root before; refused if one gets a second value. -/
def addSeen (root : ByteArray) (new : List (Nat × Nat × ByteArray)) : Seen → Option Seen
  | [] => some [(root, new)]
  | (r, old) :: l =>
    if r == root then (if agree old new then some ((r, old ++ new) :: l) else none)
    else (addSeen root new l).map fun l' => (r, old) :: l'

-- R7.14: under one root a second value at a vertex is refused, the same value and a new vertex are
-- admitted; under another root: another record: admitted. (Nothing but the root's bytes is asked:
-- which tree, chain or file it came with is no argument of addSeen.)
#guard ((addSeen zero32 [(2, 1, pattern 32)] []).bind fun s => addSeen zero32 [(2, 1, zero32)] s).isNone
#guard ((addSeen zero32 [(2, 1, pattern 32)] []).bind fun s => addSeen zero32 [(2, 1, pattern 32), (2, 2, zero32)] s).isSome
#guard ((addSeen zero32 [(2, 1, pattern 32)] []).bind fun s => addSeen (pattern 32) [(2, 1, zero32)] s).isSome
#guard (((addSeen zero32 [(2, 1, pattern 32)] []).bind fun s => addSeen (pattern 32) [(2, 1, zero32)] s).map (·.length)) == some 2 && (((addSeen zero32 [(2, 1, pattern 32)] []).bind fun s => addSeen zero32 [(2, 2, zero32)] s).map (·.length)) == some 1

def rootsOf : List ItemValue → List ByteArray
  | [] => []
  | .root d :: l => d :: rootsOf l
  | _ :: l => rootsOf l

/-! ## The reader -/

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The openings behind one draw of positions, each checked against its root and against what was
met under that root before. -/
def readOpens (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (roots : Array ByteArray)
    (poss : List Nat) (b : ByteArray) :
    List (Shape × Src) → Seen → Nat → m (Option (List (Shape × List Nat × OpenOut) × Seen × Nat))
  | [], sn, i => pure (some ([], sn, i))
  | (sh, src) :: os, sn, i =>
    let rs : Option (ByteArray × ByteArray) :=
      match src with
      | .own n => match roots[n]?, run with
        | some r, some s => some (r, s)
        | _, _ => none
      | .given r s => some (r, s)
    match rs with
    | none => pure none
    | some (root, start) => do
      let xs := listOf (poss.map (· % 2 ^ sh.a))
      match ← readOpeningW h cfg P.field P.salt sh start xs b i with
      | none => pure none
      | some o =>
        if o.root == root then
          match addSeen root (entered o.seen) sn with
          | none => pure none
          | some sn' =>
            match ← readOpens cfg P run roots poss b os sn' o.next with
            | none => pure none
            | some (l, sn'', k) => pure (some ((sh, xs, o) :: l, sn'', k))
        else pure none

/-- One round. -/
def step (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (s : St) (r : Round) : m (Option St) :=
  match slice b s.pos r.entry.msg with
  | none => pure none
  | some msg =>
    match whole (readItems P.field r.items) msg with
    | none => pure none
    | some vals =>
      match readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure none
      | some (nonce, i1) => do
        match ← Chain.queryW h s.chain msg r.kind r.entry.work nonce
            ((wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure none
        | some (c, vb) =>
          let drawn := drawRound P.field r.entry r.kind (rowOf vb)
          let l := listOf drawn.poss
          match readList P r.entry.poss l b i1 with
          | none => pure none
          | some (_, i2) =>
            let roots := s.roots ++ (rootsOf vals).toArray
            match ← readOpens h cfg P run roots drawn.poss b r.opens s.seen i2 with
            | none => pure none
            | some (cols, sn, i3) =>
              pure (some ⟨i3, c, roots, sn, s.out.push ⟨msg, vals, nonce, drawn, l, cols⟩⟩)

/-- The fold. -/
def foldRounds (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List Round → St → m (Option St)
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← step h cfg P run b s r with
    | none => pure none
    | some s' => foldRounds cfg P run b rs s'

/-- A chain in a file, from the place i on. "seen": the vertices met under each root by earlier
chains of the session (none: the empty list). -/
def readChain (S : Spec) (seen : Seen) (b : ByteArray) (i : Nat) : m (Option (ChainOut × Nat)) :=
  if !S.ok then pure none
  else
    let rnd : Option (Option ByteArray × Nat) :=
      match S.rand with
      | .inFile => (slice b i 32).map fun x => (some x, i + 32)
      | .given x => some (some x, i)
      | .none => some (none, i)
    match rnd with
    | none => pure none
    | some (x, i0) => do
      let pd ← paramsDigestW h S.params
      match ← startChainW h S.label pd S.statement x with
      | none => pure none
      | some hd =>
        match ← foldRounds h S.cfg S.plan hd.run b S.rounds
            ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
        | none => pure none
        | some s => pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos))

/-- The same, and nothing stands behind the chain. -/
def wholeChain (S : Spec) (b : ByteArray) : m (Option ChainOut) := do
  match ← readChain h S [] b 0 with
  | some (o, j) => pure (if j == b.size then some o else none)
  | none => pure none

end

/-! ## The page's known answer:
a whole chain in a file, with a tree and an opening, in both fields -/

namespace Known8

def plan (f : Fld) : Plan where
  field := f
  salt := 40
  nonce := 8
  posB := 0
  samples := 1
  saved := 1
  entries := [
    { name := "toy file: seed", msg := 32, roots := 1, drawE := 3, drawNZ := 1 },
    { name := "toy file: answer", msg := 24, answers := 1 },
    { name := "toy file: positions", work := 8, msg := 24, poss := 4, logN := 3 } ]

def spec (f : Fld) : Spec where
  label := 9
  plan := plan f
  params := paramsBytes (plan f) Toy4.cfg []
  statement := ByteArray.empty
  rand := .inFile
  cfg := Toy4.cfg
  rounds := [
    { entry := (plan f).entries.getD 0 default, kind := .seeds, items := [.root] },
    { entry := (plan f).entries.getD 1 default, kind := .nothing, items := [.answer] },
    { entry := (plan f).entries.getD 2 default, kind := .positions, items := [.e],
      opens := [({ a := 3, W := 3, tree := 0 }, .own 0)] } ]

def read (f : Fld) (b : ByteArray) : Option ChainOut := wholeChain (m := Id) formatHash (spec f) b

def file2 : ByteArray := unhex "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979cca206ba1fa1319bb2ac38000b37e987d8815c79adba4dc3afdcacc548ec933af09000000000000000900000000000000090000000000000004000000000000000500000000000000060000000000000033000000000000006500000000000000c9000000000000002d010000000000000a0d101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376797c7f6900000000000000cd000000000000002d010000000000000e1114171a1d202326292c2f3235383b3e4144474a4d505356595c5f6265686b6e7174777a7d80836a00000000000000ce000000000000002c010000000000000f1215181b1e2124272a2d303336393c3f4245484b4e5154575a5d606366696c6f7275787b7e81841d67c5cbe93ea0ec434703699e797edd6350e65886bf89bc5e0d7ed13d4f5708758fa7be2b57e74c332e61ceaddbba5977fd833c025d4248ad87372e23c6d026216df9a490f2a2ccf1792ed0bb4576c5f6e80ff092e788fadac83117e5cf29f75c9114bf586d8726460b269fdf1c6aa43da8ddba493b1fee4f61936eef2ad1be"
def file1 : ByteArray := unhex "01060b10151a1f24292e33383d42474c51565b60656a6f74797e83888d92979c7f95514c1c5007e0bc60c8534003431b2e5bc079dae999f840e7d5287454327109000000000000000900000000000000090000000000000004000000000000000500000000000000060000000000000039000000000000006500000000000000c9000000000000002d010000000000000a0d101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376797c7f6600000000000000ca000000000000002c010000000000000b0e1114171a1d202326292c2f3235383b3e4144474a4d505356595c5f6265686b6e7174777a7d806a00000000000000ce000000000000002c010000000000000f1215181b1e2124272a2d303336393c3f4245484b4e5154575a5d606366696c6f7275787b7e81846b00000000000000cf000000000000002d01000000000000101316191c1f2225282b2e3134373a3d404346494c4f5255585b5e6164676a6d707376797c7f8285abaa72b2ec6d1a4b10b4a4b15d07cef447fe8ab7b271363161957f6b1ddb938758cfcba4afff65886c763ea468be5c65d521436a91782b1265c5fa8c6fe61e37e5e4956623d169efdd6990d4f2e0883a1ed24d88fe44691bdd1994f4b38cac67"

/-- Of a chain that was read: the digest of the parameters; the root that was sent; the nonce, the
draws, the list of the last round; its opening's columns, the number of its given digests, the root
in which its walk ends. -/
def view (o : ChainOut) :
    Option (String × List String × Nat × List Nat × List Nat × List (List UInt64) × Nat × String) :=
  o.rounds[0]?.bind fun r0 => o.rounds[2]?.bind fun r2 => r2.opens.head?.map fun x =>
    (hex o.pd, (rootsOf r0.vals).map hex, r2.nonce, r2.drawn.poss, r2.list, x.2.2.cols,
      x.2.2.given.length, hex x.2.2.root)

end Known8

open Known8 in
#guard (spec .two).ok && (spec .one).ok && file2.size = 440 && file1.size = 472
-- R2.7: a column of no word, or of 2 ^ 24 words: not within the bounds; the chain as it is: within
open Known8 in
#guard (spec .two).small && !({ spec .two with rounds := (spec .two).rounds.map fun r => { r with opens := r.opens.map fun o => ({ o.1 with W := 0 }, o.2) } } : Spec).small && !({ spec .two with rounds := (spec .two).rounds.map fun r => { r with opens := r.opens.map fun o => ({ o.1 with W := 2 ^ 24 }, o.2) } } : Spec).small && !({ spec .two with rounds := (spec .two).rounds.map fun r => { r with entry := { r.entry with msg := 2 ^ 32 } } } : Spec).small
-- R7.3 as a condition on the plan: this chain opens a tree: salts of 32 bytes: not in order; of 48: in order
open Known8 in
#guard !({ spec .two with plan := { (spec .two).plan with salt := 32 }, params := paramsBytes { (spec .two).plan with salt := 32 } (spec .two).cfg [] } : Spec).ok && ({ spec .two with plan := { (spec .two).plan with salt := 48 }, params := paramsBytes { (spec .two).plan with salt := 48 } (spec .two).cfg [] } : Spec).ok
open Known8 in
#guard ((read .two file2).bind view) == some ("e3af26b56a9560ff40852beaa12cc04f8e29128c88e4bf1834fa933838d5b985", ["ca206ba1fa1319bb2ac38000b37e987d8815c79adba4dc3afdcacc548ec933af"], 51, [1, 5, 6, 5], [1, 5, 6],
  [[101, 201, 301], [105, 205, 301], [106, 206, 300]], 4, "ca206ba1fa1319bb2ac38000b37e987d8815c79adba4dc3afdcacc548ec933af")
open Known8 in
#guard ((read .one file1).bind view) == some ("9c711274b2e4b2ff0907533edefe1822a1ee11e779bca63aa9de11e0f3899f68", ["7f95514c1c5007e0bc60c8534003431b2e5bc079dae999f840e7d52874543271"], 57, [1, 7, 2, 6], [1, 2, 6, 7],
  [[101, 201, 301], [102, 202, 300], [106, 206, 300], [107, 207, 301]], 3, "7f95514c1c5007e0bc60c8534003431b2e5bc079dae999f840e7d52874543271")
-- the places of the given digests are those of the walk at the list
#guard walkPlaces 3 [1, 5, 6] = [(3, 0), (3, 4), (3, 7), (2, 1)] && walkPlaces 3 [1, 2, 6, 7] = [(3, 0), (3, 3), (2, 2)]
-- the items of the three rounds' messages
open Known8 in
#guard ((read .two file2).map fun o => o.rounds.toList.map (·.vals)) = some [[.root (unhex "ca206ba1fa1319bb2ac38000b37e987d8815c79adba4dc3afdcacc548ec933af")], [.answer (9, 9, 9)], [.e (4, 5, 6)]]
-- this library's own: altered copies of the page's file are refused: one byte short; a byte behind;
-- a bit of the random bytes, of the root, of the answer, of the element, of the nonce, of a column,
-- of a salt, of a given digest; one field's file under the other
open Known8 in
#guard (read .two (file2.extract 0 439)).isNone && (read .two (file2 ++ zeroBytes 1)).isNone && (read .one file2).isNone && (read .two file1).isNone
open Known8 in
#guard [0, 32, 64, 88, 112, 120, 144, 312, 439].all fun i => (read .two (flipAt file2 i)).isNone
open Known8 in
#guard [0, 32, 64, 88, 112, 120, 144, 376, 471].all fun i => (read .one (flipAt file1 i)).isNone

/-! ## This library's own:
the toy chain of the sections on the first query, a round's query and drawing, as a file

The file below is this library's own: the chain's random bytes, its six messages and the one nonce,
in the order of the rounds. What the reader makes of it is held against the page's known answers of
those sections. -/

namespace Toy8

def kinds : List (Kind × List Item) :=
  [(.elems, [.e, .e]), (.nothing, [.e]), (.positions, [.root]), (.seeds, []),
    (.entries, [.answer]), (.sealed, [.word])]

def spec (f : Fld) : Spec where
  label := 7
  plan := Toy4.plan f
  params := Toy4.params f
  statement := Toy4.statement
  rand := .inFile
  cfg := Toy4.cfg
  rounds :=
    ((Toy4.plan f).entries.zip kinds).map fun x => { entry := x.1, kind := x.2.1, items := x.2.2 }

/-- The file, with a given nonce, a given first coordinate of the answer in round 5 and a given word
in round 6 (both stand behind the one round with work: no later test of the chain can refuse them).
-/
def fileOf (nonce y z : Nat) : ByteArray :=
  Toy4.rnd ++ ext (4, 5, 6) ++ ext (7, 8, 9) ++ ext (1, 1, 1) ++ pattern 32 11 2 ++ u64n nonce ++
    u64n y ++ u64n 9 ++ u64n 9 ++ u64n z

def file (nonce : Nat) : ByteArray := fileOf nonce 9 77

def read (f : Fld) (b : ByteArray) : Option ChainOut := wholeChain (m := Id) formatHash (spec f) b

def roundAt (o : ChainOut) (i : Nat) : Option RoundOut := o.rounds[i]?

end Toy8

open Toy8 in
#guard (spec .two).ok && (spec .one).ok
open Toy8 in
#guard (file 116).size = 32 + 48 + 24 + 32 + 8 + 0 + 24 + 8

-- field 2: the run's value, the first value, the last value, the sealed digest, the positions as drawn and as a list, the element of round 1
open Toy8 in
#guard ((read .two (file 116)).map fun o => (o.run.map hex, hex o.rho0, hex o.rho)) =
  some (some "700cd5f8c6809036bab546f63e6fd0de6846695ee9772955436353db91d45986", "9a4c85fc23558196c3ee866b926a660f13af5df9a757f1483fcf0bb70aa3fe72", "70b365d8f0bda8f239fa4a9417b2ddddf69a25197785dd096c937c5d05064dad")
open Toy8 in
#guard ((read .two (file 116)).bind fun o => (roundAt o 5).bind fun r => r.drawn.digest.map hex) = some "0b5ec9235d31cb34c68dd2f4f50a59b3b0fd28c246389e8f59cd0350416cfdd6"
open Toy8 in
#guard ((read .two (file 116)).bind fun o => (roundAt o 2).map fun r => (r.nonce, r.drawn.poss, r.list)) = some (116, [69, 895, 454, 526, 842], [69, 454, 526, 842, 895])
open Toy8 in
#guard ((read .two (file 116)).bind fun o => (roundAt o 0).map fun r => r.drawn.elems) = some [(4610700807997304418, 4447928095050642327, 12963931155414147300)]
open Toy8 in
#guard ((read .two (file 116)).bind fun o => (roundAt o 4).map fun r => r.drawn.trits.take 8) = some [0, 1, 0, 0, -1, -1, 0, 0]

-- field 1
open Toy8 in
#guard ((read .one (file 1058)).map fun o => (o.run.map hex, hex o.rho0, hex o.rho)) =
  some (some "fd50818f742a65f3a1585c667ae07d35b3759f5e922910132b6d953d9feee385", "8ab45624b5f889e335e84864762f4b3d7e51eb87d278e34722ed12b0e114d90c", "1ded778ef215493b19c0050a0a9b93411930b82a5c1399b324c806fe0d901fb9")
open Toy8 in
#guard ((read .one (file 1058)).bind fun o => (roundAt o 5).bind fun r => r.drawn.digest.map hex) = some "dd228c00ad29dc3bb954e861ed335c21e032010f26e9813749b96bb7bad58fe6"
open Toy8 in
#guard ((read .one (file 1058)).bind fun o => (roundAt o 2).map fun r => (r.nonce, r.drawn.poss, r.list)) = some (1058, [948, 30, 628, 774, 1014], [30, 628, 774, 948, 1014])

-- Altered copies are refused
-- the file ends one byte short; a byte stands behind the chain
open Toy8 in
#guard (read .two ((file 116).extract 0 175)).isNone && (read .two ((file 116) ++ zeroBytes 1)).isNone && (read .two ByteArray.empty).isNone
-- a nonce below the least one has not the work (116 and 1058 are the least, by the page)
open Toy8 in
#guard (read .two (file 115)).isNone && (read .two (file 0)).isNone && (read .one (file 1057)).isNone
-- eight bytes that spell no element: the prime itself is refused, the prime less one is read; behind the round with work nothing but the reader of elements can refuse here
open Toy8 in
#guard (read .two (fileOf 116 18446744069414584321 77)).isNone && (read .two (fileOf 116 18446744069414584320 77)).isSome
open Toy8 in
#guard (read .one (fileOf 1058 2305843009213693951 77)).isNone && (read .one (fileOf 1058 2305843009213693950 77)).isSome
-- an item that is a word, not an element, is read whatever it is
open Toy8 in
#guard (read .two (fileOf 116 9 18446744073709551615)).isSome && (read .one (fileOf 1058 9 18446744073709551615)).isSome
-- one field's file is not the other's
open Toy8 in
#guard (read .one (file 116)).isNone && (read .two (file 1058)).isNone
-- data that are not in order are refused whatever the file: rounds that are not the plan's; a chain without random bytes that sends a root; parameters' bytes that spell another plan or another configuration
open Toy8 in
#guard (wholeChain (m := Id) formatHash { spec .two with rounds := (spec .two).rounds.dropLast } (file 116)).isNone
open Toy8 in
#guard !({ spec .two with rand := .none } : Spec).ok
open Toy8 in
#guard !({ spec .two with params := Toy4.params .one } : Spec).ok && !({ spec .two with cfg := zero32 } : Spec).ok
-- a chain without a round; a count of trees that reaches 2 ^ 16 (R7.13)
open Toy8 in
#guard !({ spec .two with plan := { Toy4.plan .two with entries := [] }, params := paramsBytes { Toy4.plan .two with entries := [] } Toy4.cfg [], rounds := [] } : Spec).ok
open Toy8 in
#guard ({ spec .two with firstTree := 65534 } : Spec).ok && !({ spec .two with firstTree := 65535 } : Spec).ok
-- R8.5: a root before a seal or before an empty message of the verifier is not in order
open Toy8 in
#guard !({ entry := { name := "x", msg := 32, roots := 1 }, kind := .sealed, items := [.root] } : Round).ok (Toy4.plan .two) false 0 false 0
open Toy8 in
#guard ({ entry := { name := "x", msg := 32, roots := 1 }, kind := .elems, items := [.root] } : Round).ok (Toy4.plan .two) false 0 false 0
-- R5.3: work before a seal or before an empty message of the verifier is not in order; without
-- work both are; before elements work is in order
open Toy8 in
#guard !({ entry := { name := "x", work := 1 }, kind := .sealed } : Round).ok (Toy4.plan .two) false 0 false 0 && !({ entry := { name := "x", work := 1 }, kind := .nothing } : Round).ok (Toy4.plan .two) false 0 false 0
open Toy8 in
#guard ({ entry := { name := "x" }, kind := .sealed } : Round).ok (Toy4.plan .two) false 0 false 0 && ({ entry := { name := "x" }, kind := .nothing } : Round).ok (Toy4.plan .two) false 0 false 0 && ({ entry := { name := "x", work := 1 }, kind := .elems } : Round).ok (Toy4.plan .two) false 0 false 0

end Fmt
