-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules7.lean: the format page's section on Merkle trees and openings (section 7), as total
functions on bytes.

The format page (docs/format/FORMAT.md, which comes with the programs, the C++ implementation that
comes with this Lean code) fixes in its section 7 what a leaf holds, how leaves and inner vertices
are hashed, and how an opening is written and checked. This file renders that section as definitions
that compute, and has every known answer that the page prints for the section as a test (this file
is not held against the page as it ships, and may differ from it). No Mathlib. It
imports Fmt/Rules1.lean (words, fields, readers), Fmt/Plan.lean (Shape) and Fmt/Rules23.lean (the
hash formatHash).

Every function that hashes is written once, over any monad m, with the hash h (number, tree, index,
start, bytes) as its first argument; its name ends in W; but for the prover's side (`upLevel`,
`build`), which calls `vertex`. The names without W are the same text at `m := Id`, `h := hId`:
these are what is run, and what all tests use.

Sources. R7.n are the page's numbers; the wording is this library's own. This file is not
held against the page as it ships, and may differ from it, for instance at R7.4, R7.14 and R7.19.



1. What the file contains, rule by rule.
   `shortPos` (R7.2): Where a mask row of length 2^b is read when the position is x: the remainder
     of x by 2^b.
   `TreeRow`, `Part`, `column` (R7.1): What a leaf holds at x: first every main row's symbol, parts
     in their order and rows in theirs; then every mask row's symbol at the short position, ordered
     alike. A symbol of the cubic extension counts as three elements.
   `PartSh`, `widthOf` (R7.1): The number W of base-field elements in a column, read off the shape.
   `saltLenOK`, `fillLen`, `saltAt`, `leafBytes` (R7.3): Column, zero bytes, salt. The zero bytes
     are there only if, with the hash's label of 16 bytes counted in, the salt would straddle a
     border between blocks of 128 bytes; they then reach up to that border.
   `leafNo`, `leafW`, `leaf` (R7.4): The digest of a leaf: number 164 (a tree of a run) or 174 (a
     stored tree; the tree of a stored table has the number 0, whichever table it is: fixed by the
     format; here the number is an argument); index 2^a + x.
     The label holds the leaf's shape: in place of the
     tree's number the hash is handed `Fmt.leafPlace`
     tree W s8 (Fmt/Rules23.lean), W the number of the column's words, s8 the salt's bytes divided
     by 8. So, on the domain, for trees' numbers below 2^16 and contents below 2^24 words
     (`leafStr_inj`, Fmt/Rules23Laws.lean), two shapes give no common hashed string.
   `bindLeafW`, `bindLeaf` (R7.18): A leaf of the tree that binds a batch's requests: number 173,
     tree 0, start cfg. Its content: the closing value of a request's first chain, 32 bytes, as four
     words; then the salt as in any leaf (no zero bytes between them: tested at all four lengths of
     a salt). What the prover puts at a place left free by the requests (as this file reads
     the page) is a rule for the
     prover alone: nothing here.
   `vertexW`, `vertex`, `vertexBW`, `vertexB` (R7.6, R7.7): An inner vertex's value from its two
     children's: number 166 (178 in the tree that binds a batch's requests), tree 0, index 0, and as
     start cfg, the configuration's digest (section 4's digest of the public files: one constant of
     the instance). What is hashed is the label and 64 bytes; neither the tree nor the place nor the
     run enters.
   walkLoneW, walkLevelW, walkW R7.9 THE WALK, WRITTEN ONCE, generic in the type of values, in how a
   parent's value is made and in where a given value is taken from. It starts from the opened leaves
   and climbs one depth at a time. On each depth it passes, in the order of places, through those
   vertices only that have an opened leaf below them. So its cost is at most (opened leaves) times
   (depth), whatever 2^a is.
   `walkPlaces`: The same walk on places alone: whose values an opening gives, in the opening's
     order.
   `listOK` (R7.8): The opened positions: at least one, strictly increasing, all below 2^a.
   `shortPosList` (R7.15): At which list a tree of depth b is opened when its group is read at a
     list over a longer range: the short positions, increasing, each once.
   `rdOpening` (R7.8): The parsing, no hash: for each opened position W elements (a word that spells
     no element is refused: R1.3) and the salt; then as many digests as `walkPlaces` names. In an
     opening the proof file gives no length, count, index or direction.
   `OpenOut`, `readOpeningW`, `readOpening` (R7.10): The verifier's part up to the comparison:
     parse, put the zero bytes in, hash the leaves in the list's order, walk. It returns the
     columns, the salts and the given digests as they stand in the opening, the root in which the
     walk ends, all vertices that the walk has met with their values (opened leaves, computed,
     given: as (depth, place, value)), and the byte behind the opening, from which a fold over a
     file goes on.
   `heapNo`, `sameValues` (R7.14): Two lists of met vertices give no vertex two values. A leaf is a
     vertex. The rule speaks of several openings under one root: the store by root and the refusal
     belong to the fold over a file (section 8's file); within one opening no vertex is met twice.
   `Record`, `enterAt`, `entered`, `enterAll` (R7.14;
   not held against the page that ships): The record of
     one root. The page keys a record by the root's 32 bytes, within a session (one run of a
     verifier that ends in one verdict): two trees that are sent with one root share it. A value is
     entered under 2^depth + place, and refused if another stands there. The value at the root stays
     out of the record. (`OpenOut.seen` lists the root: `entered` drops it.) Here a record is the
     bare list; which record an opening meets, and that only an accepted opening's values are
     entered, is the chain's reader's matter (Fmt/Rules8.lean: there `Seen`, `addSeen`; of the names
     of this row it uses `entered` alone).
   `checkOpeningW`, `checkOpening`: On a string that is to be one opening and nothing else: the root
     is the one that was sent, and no byte is left.
   `upLevel`, `build`, `rootOf`, `openingBytes` (R7.8): The prover's side, for tests and example
     provers only (these do touch all 2^a leaves).
   `Notice`, `Laid`, `layTrees` (R7.12): Which oracle messages of one prover message share a tree:
     two passes in the order of sending. A tree's parts are kept in sending order, no matter in
     which of the two passes each came. The result is none if a message has no row at all, or if a
     tree so laid has mask rows of two lengths, or longer than its main rows.
   `numberTrees` (R7.13), `takePlaces` (R7.13):
   Each chain has its own list of readable
     trees; the index of a tree in that list is called its place.
   `depthOK` (R7.16): A depth of at
   most 48: a condition on a shape. The reader of an
     opening does not test it (a description's test may).
   This library's own choices where the page is silent (a total function has to answer). A list that
   is not increasing or reaches 2^a, and a salt's length out of order, are refused. `leafBytes`,
   `leaf` and `vertex` answer on all inputs by the same formula. A list of exactly 2^16 places (0 to
   2^16 - 1) is in order (read from the
   page's program lines; no rule of the page is cited for it).

2. What is checked when the file compiles. Every known answer that the page prints for this section
is a test (#guard) (this file is not held against the page as it ships, and may differ from
it). The page's known answer on another tree under the same root (a second value at a vertex
is not admitted there either) has no test of its own: it meets the same record, so the test on a
second value at the vertex (2, 1) is that answer's too. The page's leaf under the number 174 at the
tree's number 5: as the number of a stored
table's tree is fixed at 0 it is right as a value of the hash formatHash, but it is no leaf of a lawful file
(it is outside the hash's domain: `hDom`, Fmt/Rules23.lean). For R7.15 and R7.16 the page prints
none: the tests on them are cases of this library's own making, and say so.
Guards are tests by the evaluator when the file is compiled: they leave no theorem.

3. Theorems. One small one: `fillLen_eq` (`fillLen` is `leafFill` of Fmt/Rules23.lean). Nothing else
is proved here; there is no tie to the theorem's verifier in this file.

4. What is not here.
   R7.5 and the end of R7.12 are duties of whoever gives out leaf classes, not functions of bytes.
   Of them only "mask rows of one length, not above the main rows'" is tested.
   R7.11: two opened copies of one mask symbol may differ: nothing compares them here.
   The passage from drawn positions to the list is section 6's.
   R7.4 also says that the tree of every stored table has the number 0: a rule on descriptions;
   nothing here tests it.
   R7.19 (a round whose draws are cut into parts, each part's list made from its own draws) speaks
   of a plan's entries and of section 6's lists: not rendered here.
   R7.17 (four rules on layouts: which parts may share a tree, how often a tree with a step's mask
   is opened, in which chains) is not rendered. It speaks of groups, samples and chains, which this
   section's data do not hold; by the rule itself only a program can break it, no proof can.
-/
import Fmt.Rules1
import Fmt.Plan
import Fmt.Rules23

namespace Fmt

/-! ### The leaves -/

/-- R7.2. -/
def shortPos (x b : Nat) : Nat := x % 2 ^ b

/-- A row: its symbol at a position, as one or three elements of the base field. -/
abbrev TreeRow : Type := Nat → List UInt64

/-- What one oracle message, or a part of one, lays into a tree. -/
structure Part where
  main : List TreeRow
  mask : List TreeRow

/-- R7.1; the mask rows have the length 2^b. -/
def column (b : Nat) (parts : List Part) (x : Nat) : List UInt64 :=
  (parts.flatMap fun p => p.main.flatMap fun r => r x) ++
    (parts.flatMap fun p => p.mask.flatMap fun r => r (shortPos x b))

/-- The shape of a part: for each main row and for each mask row, whether its symbols lie in the
extension field. -/
structure PartSh where
  main : List Bool
  mask : List Bool

def symLen (ext : Bool) : Nat := if ext then 3 else 1

/-- R7.1: the number of elements in a column. -/
def widthOf (parts : List PartSh) : Nat :=
  parts.foldl (fun n p => p.main.foldl (fun n e => n + symLen e) n) 0 +
    parts.foldl (fun n p => p.mask.foldl (fun n e => n + symLen e) n) 0

/-- R7.3: a salt's number of bytes. -/
def saltLenOK (s : Nat) : Bool := s % 8 == 0 && decide (40 ≤ s) && decide (s ≤ 64)

/-- A list of elements, 8 bytes each. -/
def colBytes (col : List UInt64) : ByteArray := cat (col.map u64)

/-- R7.3: how many zero bytes stand between W elements and a salt of s bytes. -/
def fillLen (W s : Nat) : Nat :=
  if (16 + 8 * W) % 128 + s ≤ 128 then 0 else 128 - (16 + 8 * W) % 128

/-- The fill is the one of which the hash's domain speaks (Fmt/Rules23.lean). -/
theorem fillLen_eq (W s : Nat) : fillLen W s = leafFill W s := rfl

/-- The byte of a leaf at which the salt begins. -/
def saltAt (W s : Nat) : Nat := 8 * W + fillLen W s

/-- R7.3. -/
def leafBytes (col : List UInt64) (salt : ByteArray) : ByteArray :=
  colBytes col ++ zeroBytes (fillLen col.length salt.size) ++ salt

/-- R7.4: the number under which a tree's leaves are hashed. -/
def leafNo (stored : Bool) : Nat := if stored then 174 else 164

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- R7.4, with R2.1:
in the label's first word, above the tree's number, stand the
number of the column's words and the number of the salt's words. -/
def leafW (number tree a x : Nat) (start : ByteArray) (col : List UInt64) (salt : ByteArray) :
    m ByteArray :=
  h number (leafPlace tree col.length (salt.size / 8)) (2 ^ a + x) start (leafBytes col salt)

/-- R7.18: a leaf of a batch's binding tree: number 173, tree 0, the configuration's digest as the
start; its content is the closing value of a request's first chain, 32 bytes, which count as four
words. -/
def bindLeafW (depth place : Nat) (cfg closing salt : ByteArray) : m ByteArray :=
  leafW h 173 0 depth place cfg ((List.range 4).map fun i => wordAt closing (8 * i)) salt

/-- R7.7; cfg: the configuration's digest. -/
def vertexW (cfg left right : ByteArray) : m ByteArray := h 166 0 0 cfg (left ++ right)

/-- R7.7, in the tree that binds a batch's requests. -/
def vertexBW (cfg left right : ByteArray) : m ByteArray := h 178 0 0 cfg (left ++ right)

end

/-! ### The walk -/

section
variable {m : Type → Type}
  [Monad m] {α σ : Type} (comb : Nat → Nat → α → α → m α) (give : Nat → Nat → σ → Option (α × σ))

/-- A vertex (d, i) whose sibling has no opened leaf below it: the sibling's value is given. -/
def walkLoneW (d i : Nat) (x : α) (s : σ) : m (Option ((Nat × α) × σ)) :=
  match give d (if i % 2 == 0 then i + 1 else i - 1) s with
  | none => pure none
  | some (o, s') => do
    let v ← if i % 2 == 0 then comb (d - 1) (i / 2) x o else comb (d - 1) (i / 2) o x
    pure (some ((i / 2, v), s'))

/-- R7.9, one depth. The list holds (place, value) for the vertices of depth d that have an opened
leaf below them, places increasing. comb d' i l r makes the value of (d', i) from its children's;
give d i hands out the next given value, which stands for the vertex (d, i). -/
def walkLevelW (d : Nat) : List (Nat × α) → σ → m (Option (List (Nat × α) × σ))
  | [], s => pure (some ([], s))
  | [(i, x)], s => do
    let r ← walkLoneW comb give d i x s
    pure (r.map fun r => ([r.1], r.2))
  | (i, x) :: (i', x') :: rest, s =>
    if i % 2 == 0 && i' == i + 1 then do
      let v ← comb (d - 1) (i / 2) x x'
      let r ← walkLevelW d rest s
      pure (r.map fun r => ((i / 2, v) :: r.1, r.2))
    else do
      match ← walkLoneW comb give d i x s with
      | none => pure none
      | some (p, s') =>
        let r ← walkLevelW d ((i', x') :: rest) s'
        pure (r.map fun r => (p :: r.1, r.2))

/-- R7.9: from depth d to the root; none if a given value lacks or the list was empty. met: the
vertices passed so far, as (depth, place, value); those of the present depth are put in front. -/
def walkW :
    Nat → List (Nat × α) → σ → List (Nat × Nat × α) → m (Option (α × σ × List (Nat × Nat × α)))
  | 0, [(i, r)], s, met => pure (some (r, s, (0, i, r) :: met))
  | 0, _, _, _ => pure none
  | d + 1, now, s, met => do
    match ← walkLevelW comb give (d + 1) now s with
    | none => pure none
    | some (nxt, s') => walkW d nxt s' (now.map (fun v => (d + 1, v.1, v.2)) ++ met)

end

/-- Whose values an opening gives, in the opening's order, as (depth, place). -/
def walkPlaces (a : Nat) (xs : List Nat) : List (Nat × Nat) :=
  match Id.run
      (walkW (m := Id) (α := Unit) (σ := List (Nat × Nat)) (fun _ _ _ _ => pure ())
        (fun d i acc => some ((), (d, i) :: acc)) a (xs.map fun x => (x, ())) [] []) with
  | some (_, acc, _) => acc.reverse
  | none => []

/-- R7.8: at least one position, increasing, below 2^a. -/
def listOK (a : Nat) : List Nat → Bool
  | [] => false
  | [x] => decide (x < 2 ^ a)
  | x :: y :: tl => decide (x < y) && listOK a (y :: tl)

/-- Numbers as a list: increasing, each once. -/
def sortedOnce (l : List Nat) : List Nat :=
  l.foldl
    (fun acc x => if acc.contains x then acc else acc.filter (· < x) ++ [x] ++ acc.filter (x < ·))
    []

/-- R7.15. -/
def shortPosList (b : Nat) (xs : List Nat) : List Nat := sortedOnce (xs.map fun x => shortPos x b)

/-! ### The verifier -/

/-- R7.8: the parsing: (column, salt) for each opened position, then the given digests. -/
def rdOpening (f : Fld) (salt : Nat) (sh : Shape) (xs : List Nat) :
    Rd (List (List UInt64 × ByteArray) × List ByteArray) :=
  rdPair (rdMany (rdPair (rdMany (rdElt f) sh.W) (rdBytes salt)) xs.length)
    (rdMany rdDigest (walkPlaces sh.a xs).length)

/-- What the reader of an opening hands on. -/
structure OpenOut where
  /-- The columns, in the list's order. -/
  cols : List (List UInt64)
  /-- The opening's salts, in the list's order. -/
  salts : List ByteArray
  /-- The given digests, in the walk's order: exactly those that the walk takes. -/
  given : List ByteArray
  /-- The root in which the walk ends. -/
  root : ByteArray
  /-- Every vertex that the walk has met, as (depth, place, value): the opened leaves, the computed
  ones with the root, the given ones. -/
  seen : List (Nat × Nat × ByteArray)
  /-- The byte behind the opening. -/
  next : Nat

/-- The next given digest; it is noted for which vertex it stands. -/
def takeGiven {α : Type} (d i : Nat) (s : List α × List (Nat × Nat × α)) :
    Option (α × List α × List (Nat × Nat × α)) :=
  match s.1 with
  | [] => none
  | x :: g => some (x, g, (d, i, x) :: s.2)

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The opened leaves' digests, in the list's order, each with its place. -/
def leavesW (sh : Shape) (start : ByteArray) :
    List Nat → List (List UInt64 × ByteArray) → m (List (Nat × ByteArray))
  | x :: xs, (col, salt) :: cs => do
    let v ← leafW h (leafNo sh.stored) sh.tree sh.a x start col salt
    let r ← leavesW sh start xs cs
    pure ((x, v) :: r)
  | _, _ => pure []

/-- R7.10 up to the comparison: an opening that begins at the byte i of b. The configuration's
digest, the field, the salt's length, the shape, the start and the list are the verifier's own.
none: refused. -/
def readOpeningW (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) : m (Option OpenOut) :=
  if listOK sh.a xs && saltLenOK salt then
    match rdOpening f salt sh xs b i with
    | none => pure none
    | some ((cs, given), next) => do
      let now ← leavesW h sh start xs cs
      let r ← walkW (fun _ _ l r => vertexW h cfg l r) takeGiven sh.a now (given, []) []
      pure (r.map fun r => ⟨cs.map (·.1), cs.map (·.2), given, r.1, r.2.2 ++ r.2.1.2, next⟩)
  else pure none

/-- R7.10 on a string that is to be one opening and nothing else. -/
def checkOpeningW (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start root : ByteArray)
    (xs : List Nat) (opening : ByteArray) :
    m (Option (List (List UInt64))) := do
  match ← readOpeningW h cfg f salt sh start xs opening 0 with
  | some o => pure (if o.root = root ∧ o.next = opening.size then some o.cols else none)
  | none => pure none

end

/-- A vertex's number in the heap order: the root is 1. -/
def heapNo (d i : Nat) : Nat := 2 ^ d + i

/-- R7.14: no vertex has one value in the first list and another in the second. The key is (depth,
place), that is, the heap number; never a digest's value. -/
def sameValues (s t : List (Nat × Nat × ByteArray)) : Bool :=
  s.all fun v => t.all fun w => v.1 != w.1 || v.2.1 != w.2.1 || decide (v.2.2 = w.2.2)

/-- R7.14: the record of one root: the values met so far under it, keyed by the heap number. -/
abbrev Record : Type := List (Nat × ByteArray)

/-- R7.14: a value is entered at a vertex; none: this vertex has another value under this root
already. -/
def enterAt (rec : Record) (d i : Nat) (v : ByteArray) : Option Record :=
  match rec.lookup (heapNo d i) with
  | some w => if w = v then some rec else none
  | none => some ((heapNo d i, v) :: rec)

/-- R7.14: what of an opening's met vertices is entered: all but the root's own value. -/
def entered (seen : List (Nat × Nat × ByteArray)) : List (Nat × Nat × ByteArray) :=
  seen.filter fun v => v.1 != 0

/-- R7.14: all that an opening has met, but for the root's own value (`entered`), is entered. -/
def enterAll (rec : Record) (seen : List (Nat × Nat × ByteArray)) : Option Record :=
  (entered seen).foldl (fun r v => r.bind fun r => enterAt r v.1 v.2.1 v.2.2) (some rec)

/-! ### The same at the hash formatHash -/

/-- formatHash as a hash in the monad Id. -/
def hId : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun number tree index start bytes => pure (formatHash number tree index start bytes)

def leaf (number tree a x : Nat) (start : ByteArray) (col : List UInt64) (salt : ByteArray) :
    ByteArray :=
  Id.run (leafW hId number tree a x start col salt)
def bindLeaf (depth place : Nat) (cfg closing salt : ByteArray) : ByteArray :=
  Id.run (bindLeafW hId depth place cfg closing salt)
def vertex (cfg left right : ByteArray) : ByteArray := Id.run (vertexW hId cfg left right)
def vertexB (cfg left right : ByteArray) : ByteArray := Id.run (vertexBW hId cfg left right)
def readOpening (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start : ByteArray)
    (xs : List Nat) (b : ByteArray) (i : Nat) : Option OpenOut :=
  Id.run (readOpeningW hId cfg f salt sh start xs b i)
def checkOpening (cfg : ByteArray) (f : Fld) (salt : Nat) (sh : Shape) (start root : ByteArray)
    (xs : List Nat) (opening : ByteArray) : Option (List (List UInt64)) :=
  Id.run (checkOpeningW hId cfg f salt sh start root xs opening)

/-! ### The prover's side, for the guards and for example provers -/

/-- The values of depth d from those of depth d + 1. -/
def upLevel (cfg : ByteArray) : List ByteArray → List ByteArray
  | l :: r :: tl => vertex cfg l r :: upLevel cfg tl
  | _ => []

/-- All values: the first list is depth 0 (the root alone), the last is depth a (the leaves). -/
def build (cfg : ByteArray) : Nat → List ByteArray → List (List ByteArray)
  | 0, leaves => [leaves]
  | d + 1, leaves => build cfg d (upLevel cfg leaves) ++ [leaves]

def rootOf (values : List (List ByteArray)) : ByteArray := (values.headD []).headD ByteArray.empty

/-- R7.8: an opening's bytes, from the columns, the salts and all values. -/
def openingBytes (a : Nat) (col : Nat → List UInt64) (salt : Nat → ByteArray)
    (values : List (List ByteArray)) (xs : List Nat) : ByteArray :=
  cat (xs.map fun x => colBytes (col x) ++ salt x) ++
    cat ((walkPlaces a xs).map fun v => (values.getD v.1 []).getD v.2 ByteArray.empty)

/-! ### Laying the trees -/

/-- What the rule looks at in an oracle message's notice: its leaf class; a, if it has main rows, of
length 2^a; b, if it has mask rows, of length 2^b. -/
structure Notice where
  cls  : Nat
  main : Option Nat
  mask : Option Nat

/-- A tree as it is laid: its class; its main rows' a, if it has main rows; the oracle messages in
it, by their numbers in the order of sending. -/
structure Laid where
  cls   : Nat
  main  : Option Nat
  parts : List Nat
  deriving DecidableEq, Repr

/-- The message k joins the first tree that fits, or opens a new one behind all. -/
def joinFirst (fits : Laid → Bool) (new : Laid) (k : Nat) : List Laid → List Laid
  | [] => [new]
  | t :: ts =>
    if fits t then { t with parts := t.parts.filter (· < k) ++ [k] ++ t.parts.filter (k < ·) } :: ts
    else t :: joinFirst fits new k ts

/-- The members of a list, numbered from k on. -/
def numbered {β : Type} : Nat → List β → List (Nat × β)
  | _, [] => []
  | k, x :: xs => (k, x) :: numbered (k + 1) xs

/-- R7.12: the two passes. -/
def layRaw (ms : List Notice) : List Laid :=
  let one := (numbered 0 ms).foldl (fun ts n => match n.2.main with
    | some a =>
      joinFirst (fun t => t.cls == n.2.cls && t.main == some a) ⟨n.2.cls, some a, [n.1]⟩ n.1 ts
    | none => ts) []
  (numbered 0 ms).foldl (fun ts n => match n.2.main with
    | some _ => ts
    | none => joinFirst (fun t => t.cls == n.2.cls) ⟨n.2.cls, none, [n.1]⟩ n.1 ts) one

/-- The b's of the mask rows in a tree. -/
def maskLens (ms : List Notice) (t : Laid) : List Nat :=
  t.parts.filterMap fun k => (ms[k]?).bind (·.mask)

/-- A tree's mask rows have one length, not above that of its main rows; a tree holds some row. -/
def laidOK (ms : List Notice) (t : Laid) : Bool :=
  match maskLens ms t with
  | [] => t.main.isSome
  | b :: bs => bs.all (· == b) && (match t.main with
    | some a => decide (b ≤ a)
    | none => true)

/-- R7.12: the trees of one prover message, in the order in which `joinFirst` begins them; none if
the shape is no shape of the format. -/
def layTrees (ms : List Notice) : Option (List Laid) :=
  if (ms.all fun n => n.main.isSome || n.mask.isSome) && (layRaw ms).all (laidOK ms) then
    some (layRaw ms)
  else none

/-- The depth of a tree as laid. -/
def Laid.depth (ms : List Notice) (t : Laid) : Nat :=
  match t.main with
  | some a => a
  | none => (maskLens ms t).headD 0

/-- R7.13: a chain's new trees, prover message by prover message, numbered from "first" on: 0, or
the length of the list of the chain that this one continues; none if the list would have more than
2^16 places. -/
def numberTrees (first : Nat) (perMessage : List (List Laid)) : Option (List (Nat × Laid)) :=
  if first + perMessage.flatten.length ≤ 2 ^ 16 then some (numbered first perMessage.flatten)
  else none

/-- R7.13: the places that
a chain's list takes, event by event: some l: a prover's
message sends the trees l; none: the chain adopts one tree of another chain. "first": the places
that the list has at the chain's beginning. For a message the places taken are its trees' numbers;
an adopted tree uses a place up, and its leaves go on carrying its old number. none if the list
would have more than 2^16 places. -/
def takePlaces (first : Nat) (events : List (Option (List Laid))) : Option (List (List Nat)) :=
  let go := events.foldl (fun (s : Nat × List (List Nat)) e => let n := (e.map List.length).getD 1; (s.1 + n, s.2 ++ [(List.range n).map (s.1 + ·)])) (first, [])
  if go.1 ≤ 2 ^ 16 then some go.2 else none

/-- R7.16: no tree is
deeper than 48. A condition on a shape, which is public: the reader
of an opening does not test it. -/
def depthOK (a : Nat) : Bool := decide (a ≤ 48)

/-! ### The page's known answers -/

/-- The column 1 .. n. -/
def k7Col (n : Nat) : List UInt64 := (List.range n).map fun i => UInt64.ofNat (i + 1)
def k7Salt : ByteArray := pattern 40 3 9
def k7Start : ByteArray := pattern 32 5 1

#guard (leafBytes (k7Col 3) k7Salt).size = 64 ∧ saltAt 3 40 = 24
#guard hex (leaf 164 5 3 6 k7Start (k7Col 3) k7Salt) = "89599a66474b3e68f883f399255ec7b4d1c225bc7348803919c6f927af0bc5b1"
#guard (leafBytes (k7Col 9) k7Salt).size = 112 ∧ saltAt 9 40 = 72
#guard hex (leaf 164 5 3 6 k7Start (k7Col 9) k7Salt) = "7b1b85a527dfe724e22bb335a49faa2afe869afea2ce46df1eec65fb0bb7959b"
#guard (leafBytes (k7Col 10) k7Salt).size = 152 ∧ saltAt 10 40 = 112
#guard hex (leaf 164 5 3 6 k7Start (k7Col 10) k7Salt) = "a2a01d576f6706338289077464979d99bf0a39a1843a90f0a946b4cbefb802fd"
#guard (leafBytes (k7Col 11) k7Salt).size = 152 ∧ saltAt 11 40 = 112
#guard hex (leaf 164 5 3 6 k7Start (k7Col 11) k7Salt) = "752ecd9d24f770ccec747c2fa279896f14cfa420de9e66ad38d73d5ae69d1d39"
#guard (leafBytes (k7Col 14) k7Salt).size = 152 ∧ saltAt 14 40 = 112
#guard hex (leaf 164 5 3 6 k7Start (k7Col 14) k7Salt) = "1ef4886b1ccce41a2c5453d7e4e31851c3e5a0f99a9327a8153af0c2aea3ae23"
#guard (leafBytes (k7Col 16) k7Salt).size = 168 ∧ saltAt 16 40 = 128
#guard hex (leaf 164 5 3 6 k7Start (k7Col 16) k7Salt) = "e8572aca9c485ebe7be99e5e2ca5c4c44d1fc634cce9608d1dee6bd65124e7b7"
#guard (leafBytes (k7Col 25) k7Salt).size = 240 ∧ saltAt 25 40 = 200
#guard hex (leaf 164 5 3 6 k7Start (k7Col 25) k7Salt) = "079b3341eb5ae565717ce9ddc4fb799cb19b0be92b288381621afe0b98506a23"
#guard (leafBytes (k7Col 26) k7Salt).size = 280 ∧ saltAt 26 40 = 240
#guard hex (leaf 164 5 3 6 k7Start (k7Col 26) k7Salt) = "5f48eb1e7378694660beed0b819bceadedfccf653603e6e571869fb8ff437b22"
-- two shapes that would give one hashed string if the label did not hold the leaf's shape (the eleventh word 0 is the first word of the fill): other digests
#guard leafBytes (k7Col 10) k7Salt = leafBytes (k7Col 10 ++ [0]) k7Salt ∧ leaf 164 5 3 6 k7Start (k7Col 10) k7Salt ≠ leaf 164 5 3 6 k7Start (k7Col 10 ++ [0]) k7Salt
-- a binding leaf: depth 2, place 3
#guard hex (bindLeaf 2 3 k7Start (pattern 32) k7Salt) = "0b573addb4922151823d80974c91e8697c33ff51bf4acf7de4ff96434c05ce86"
#guard [40, 48, 56, 64].all fun s => fillLen 4 s == 0
#guard hex (leaf 174 5 3 6 k7Start (k7Col 3) k7Salt) = "84b96cb0a80277e5e457ebff61e584eed58ffda811e028e9e9e782b9a9feb539"

/-- The page's tree: two main rows of length 2^3, one mask row of length 2^1, number 5, made in a
run. -/
def k7Parts : List Part :=
  [⟨[fun x => [UInt64.ofNat (100 + x)], fun x => [UInt64.ofNat (200 + x)]],
    [fun x => [UInt64.ofNat (300 + x)]]⟩]
def k7Column (x : Nat) : List UInt64 := column 1 k7Parts x
def k7SaltAt (x : Nat) : ByteArray := pattern 40 3 (9 + x)
def k7Shape : Shape := { a := 3, W := 3, tree := 5 }
/-- The configuration's digest of one public file: the three letters toy and a line feed. -/
def k7Cfg : ByteArray := unhex "e7b508817ead50bb3f386f68d442b114119e93e8ef2b14a7d70190075348db5f"
def k7Values : List (List ByteArray) :=
  build k7Cfg 3 ((List.range 8).map fun x => leaf 164 5 3 x k7Start (k7Column x) (k7SaltAt x))
def k7Root : ByteArray := rootOf k7Values
def k7Open (drawn : List Nat) : ByteArray :=
  openingBytes 3 k7Column k7SaltAt k7Values (sortedOnce drawn)

#guard widthOf [⟨[false, false], [false]⟩] = 3 ∧ widthOf [⟨[true, false], []⟩, ⟨[], [true]⟩] = 7
#guard k7Column 6 = [106, 206, 300] ∧ k7Column 5 = [105, 205, 301]
#guard formatHash 169 0 2 zero32 (u64n 1 ++ text (ascii "toy\n")) = k7Cfg
#guard hex (vertex (pattern 32) (pattern 32) ((pattern 64).extract 32 64)) = "af2a19aa20cc89e1e740e2ec4d34a275eae7bff385fcfc64e3064ccd7cc1b3f8"
#guard hex k7Root = "8b1dfb42026fa0ae230796bf9b8a7f2dfe20a0b84aaa97c945bb74fdf96e912a"
#guard walkPlaces 3 (sortedOnce [6, 1, 6, 3]) = [(3, 0), (3, 2), (3, 7), (2, 2)]
#guard (k7Open [6, 1, 6, 3]).size = 320 ∧ hex (formatHash 168 0 0 zero32 (k7Open [6, 1, 6, 3])) = "4399892d97c5affcfccacb46f45b4daa1931aca115231a14b99fc878c6219ef5"
#guard walkPlaces 3 (sortedOnce [5]) = [(3, 4), (2, 3), (1, 0)]
#guard (k7Open [5]).size = 160 ∧ hex (formatHash 168 0 0 zero32 (k7Open [5])) = "f76bb7cb11221878e021ead7b67aa4229c794710db9f994eca0213f6bca2a12f"
#guard walkPlaces 3 (sortedOnce [0, 4, 2, 6]) = [(3, 1), (3, 3), (3, 5), (3, 7)]
#guard (k7Open [0, 4, 2, 6]).size = 384 ∧ hex (formatHash 168 0 0 zero32 (k7Open [0, 4, 2, 6])) = "db1b4634cb60fceae52c3245d7bbe56930d2aff6268d5658a94f24cde595fde3"
#guard walkPlaces 3 (sortedOnce [2, 3]) = [(2, 0), (1, 1)]
#guard (k7Open [2, 3]).size = 192 ∧ hex (formatHash 168 0 0 zero32 (k7Open [2, 3])) = "bebd1a24db8f6a253efdcdc56ee06156e3d6456086019e986536dcfac0e3895b"

/-! ### Guards of this library's own making:
the verifier on the page's four openings, and on altered copies; the page's known answers on
R7.14 -/

/-- The lowest bit of one byte of a string changed. -/
def flipAt (b : ByteArray) (i : Nat) : ByteArray :=
  b.extract 0 i ++ ⟨#[byteAt b i ^^^ 1]⟩ ++ b.extract (i + 1) b.size

#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [1, 3, 6] (k7Open [6, 1, 6, 3]) = some [k7Column 1, k7Column 3, k7Column 6]
#guard checkOpening k7Cfg .one 40 k7Shape k7Start k7Root [5] (k7Open [5]) = some [k7Column 5]
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [0, 2, 4, 6] (k7Open [0, 4, 2, 6]) = some [k7Column 0, k7Column 2, k7Column 4, k7Column 6]
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] (k7Open [2, 3]) = some [k7Column 2, k7Column 3]
-- refused: a byte of a column, of a salt, of a given digest changed; a byte too many; a byte too few; another list; another tree's number; another start; the stored trees' number
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] (flipAt (k7Open [2, 3]) 0) = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] (flipAt (k7Open [2, 3]) 30) = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] (flipAt (k7Open [2, 3]) 191) = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] (k7Open [2, 3] ++ zeroBytes 1) = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 3] ((k7Open [2, 3]).extract 0 191) = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [2, 4] (k7Open [2, 3]) = none
#guard checkOpening k7Cfg .two 40 { k7Shape with tree := 6 } k7Start k7Root [2, 3] (k7Open [2, 3]) = none
#guard checkOpening k7Cfg .two 40 k7Shape (pattern 32) k7Root [2, 3] (k7Open [2, 3]) = none
#guard checkOpening k7Cfg .two 40 { k7Shape with stored := true } k7Start k7Root [2, 3] (k7Open [2, 3]) = none
-- refused: the empty list; a list that does not increase; a position at 2^a; a salt's length out of order
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [] ByteArray.empty = none
#guard checkOpening k7Cfg .two 40 k7Shape k7Start k7Root [3, 2] (k7Open [2, 3]) = none
#guard listOK 3 [7] = true ∧ listOK 3 [8] = false ∧ listOK 3 [2, 2] = false
#guard saltLenOK 32 = false ∧ saltLenOK 40 = true ∧ saltLenOK 44 = false ∧ saltLenOK 64 = true ∧ saltLenOK 72 = false
-- a word that spells no element of the field is refused before any hash (R1.3)
#guard (rdOpening .one 40 { a := 0, W := 1, tree := 0 } [0] (u64n (2 ^ 61 - 1) ++ zeroBytes 40) 0).isNone = true
#guard (rdOpening .one 40 { a := 0, W := 1, tree := 0 } [0] (u64n (2 ^ 61 - 2) ++ zeroBytes 40) 0).isSome = true
-- an opening inside a longer string: the byte behind it
#guard (readOpening k7Cfg .two 40 k7Shape k7Start [2, 3] (zeroBytes 7 ++ k7Open [2, 3] ++ zeroBytes 9) 7).map (·.next) = some 199
-- the salts and the given digests are handed on as they stand in the opening
#guard (readOpening k7Cfg .two 40 k7Shape k7Start [2, 3] (k7Open [2, 3]) 0).map (fun o => (o.salts, o.given)) = some ([k7SaltAt 2, k7SaltAt 3], [(k7Values.getD 2 []).getD 0 ByteArray.empty, (k7Values.getD 1 []).getD 1 ByteArray.empty])
-- R7.16: depth 0: the root is the leaf's digest
#guard (readOpening k7Cfg .two 40 { a := 0, W := 3, tree := 5 } k7Start [0] (colBytes (k7Col 3) ++ k7Salt) 0).map (·.root) = some (leaf 164 5 0 0 k7Start (k7Col 3) k7Salt)
-- the walk passes through vertices over opened leaves only: a tree of depth 40, one position
#guard (walkPlaces 40 [2 ^ 39 + 5]).length = 40

/-- The page's leaves under another configuration's digest. -/
def k7Other : List (List ByteArray) := build (pattern 32) 3 (k7Values.getD 3 [])

-- another configuration: the verifier and the prover's side agree with each other under it; the root is another; under the page's configuration that opening is refused
#guard checkOpening (pattern 32) .two 40 k7Shape k7Start (rootOf k7Other) [1, 3, 6] (openingBytes 3 k7Column k7SaltAt k7Other [1, 3, 6]) = some [k7Column 1, k7Column 3, k7Column 6]
#guard rootOf k7Other ≠ k7Root
#guard checkOpening k7Cfg .two 40 k7Shape k7Start (rootOf k7Other) [1, 3, 6] (openingBytes 3 k7Column k7SaltAt k7Other [1, 3, 6]) = none

/-- A tree whose leaves over one short position disagree in the mask row's symbol. -/
def k7Odd (x : Nat) : List UInt64 :=
  [UInt64.ofNat (100 + x), UInt64.ofNat (200 + x), UInt64.ofNat (300 + x)]
def k7OddValues : List (List ByteArray) :=
  build k7Cfg 3 ((List.range 8).map fun x => leaf 164 5 3 x k7Start (k7Odd x) (k7SaltAt x))

-- R7.11: positions 1 and 3 lie over one short position; the opening is accepted all the same
#guard checkOpening k7Cfg .two 40 k7Shape k7Start (rootOf k7OddValues) [1, 3] (openingBytes 3 k7Odd k7SaltAt k7OddValues [1, 3]) = some [k7Odd 1, k7Odd 3]

/-- What the walk has met, as (depth, place, value). -/
def k7Seen (xs : List Nat) : List (Nat × Nat × ByteArray) :=
  ((readOpening k7Cfg .two 40 k7Shape k7Start xs (k7Open xs) 0).map (·.seen)).getD []

-- what is met at the list [2, 3]: two leaves, their parent, its parent, the root; and the two given ones
#guard (k7Seen [2, 3]).map (fun v => (v.1, v.2.1)) = [(0, 0), (1, 0), (2, 1), (3, 2), (3, 3), (1, 1), (2, 0)]
#guard (k7Seen [1, 3, 6]).all fun v => decide ((k7Values.getD v.1 []).getD v.2.1 ByteArray.empty = v.2.2)
-- R7.14: two honest openings under one root agree wherever they meet; a value changed at a vertex that both meet is seen
-- The page's known answers on R7.14 (five lines; for how far they are held, see the head under
-- Sources): the honest openings at 1 3 6 and then
-- at 3 5: 22 values entered, all admitted; 14 vertices in the record; then the vertex (2, 1) given
-- as 32 zero bytes: not admitted; the same at another tree whose root is the same 32 bytes: not
-- admitted: the same record, so the third guard is that line's too; the same under another root (a
-- fresh record): admitted: the fourth guard
#guard (entered (k7Seen [1, 3, 6])).length + (entered (k7Seen [3, 5])).length = 22
#guard (((enterAll [] (k7Seen [1, 3, 6])).bind fun r => enterAll r (k7Seen [3, 5])).map List.length) = some 14
#guard (((enterAll [] (k7Seen [1, 3, 6])).bind fun r => enterAll r (k7Seen [3, 5])).bind fun r => enterAt r 2 1 zero32) = none
#guard (enterAt [] 2 1 zero32).isSome
#guard sameValues (k7Seen [2, 3]) (k7Seen [1, 3, 6]) = true
#guard sameValues (k7Seen [2, 3]) ((k7Seen [1, 3, 6]).map fun v => if v.1 = 1 ∧ v.2.1 = 1 then (v.1, v.2.1, zero32) else v) = false

/-! ### Guards of this library's own making:
laying and numbering (the page prints none for R7.15 and R7.16), and the page's known answers on
R7.12, R7.13 -/

-- five messages: (class 1, main 2^4), (class 1, masks 2^2 alone), (class 1, main 2^3), (class 2, masks 2^2 alone), (class 1, main 2^4 with masks 2^2)
#guard layTrees [⟨1, some 4, none⟩, ⟨1, none, some 2⟩, ⟨1, some 3, none⟩, ⟨2, none, some 2⟩, ⟨1, some 4, some 2⟩] = some [⟨1, some 4, [0, 1, 4]⟩, ⟨1, some 3, [2]⟩, ⟨2, none, [3]⟩]
-- mask rows of two lengths in one tree; mask rows longer than the main rows: no shape of the format
#guard layTrees [⟨1, some 4, some 2⟩, ⟨1, none, some 3⟩] = none
#guard layTrees [⟨1, some 2, some 3⟩] = none
/-- The page's chain of three prover's messages, each laid into its trees. -/
def k7Chain : Option (List (List Laid)) :=
  match layTrees
      [⟨1, some 4, none⟩, ⟨1, none, some 2⟩, ⟨1, some 3, none⟩,
        ⟨2, none, some 2⟩, ⟨1, some 4, some 2⟩],
    layTrees [⟨1, some 4, none⟩],
    layTrees [⟨1, none, some 2⟩, ⟨2, none, some 2⟩, ⟨1, none, some 2⟩] with
  | some a, some b, some c => some [a, b, c]
  | _, _, _ => none

-- The page's known answers on R7.12, R7.13 (at another edition than the one that
-- ships): a notice: (leaf class, a, b)
#guard (layTrees [⟨1, some 4, none⟩, ⟨1, none, some 2⟩, ⟨1, some 3, none⟩, ⟨2, none, some 2⟩, ⟨1, some 4, some 2⟩]).map (·.map (·.parts)) = some [[0, 1, 4], [2], [3]]
#guard (layTrees [⟨3, none, some 2⟩, ⟨3, some 5, some 2⟩, ⟨3, none, some 2⟩]).map (·.map (·.parts)) = some [[0, 1, 2]]
#guard (layTrees [⟨1, none, some 2⟩, ⟨2, none, some 2⟩, ⟨1, none, some 2⟩]).map (·.map (·.parts)) = some [[0, 2], [1]]
#guard (k7Chain.map fun l => (numberTrees 0 l).map (·.map (·.1))) = some (some [0, 1, 2, 3, 4, 5]) ∧ (k7Chain.map (·.map List.length)) = some [3, 1, 2]
#guard ((layTrees [⟨1, some 4, none⟩]).map fun l => (numberTrees 6 [l]).map (·.map (·.1))) = some (some [6])
-- a message without any row, also one that would join a tree with rows: no shape of the format
#guard layTrees [⟨1, some 4, none⟩, ⟨1, none, none⟩] = none ∧ layTrees [⟨1, none, none⟩] = none
-- five cases that a program of this library's own, written from the rule's words and not
-- from this file, answered; this file answers alike. (It answers the case above alike too,
-- but not independently.)
#guard (layTrees [⟨1, none, some 2⟩]).map (·.map (·.parts)) = some [[0]]
#guard (layTrees [⟨1, none, some 2⟩, ⟨1, some 4, none⟩]).map (·.map (·.parts)) = some [[0, 1]]
#guard (layTrees [⟨1, some 4, none⟩, ⟨1, some 3, none⟩, ⟨1, none, some 2⟩]).map (·.map (·.parts)) = some [[0, 2], [1]]
#guard (layRaw [⟨1, some 4, some 1⟩, ⟨1, none, some 2⟩]).map (·.parts) = [[0, 1]] ∧ layTrees [⟨1, some 4, some 1⟩, ⟨1, none, some 2⟩] = none
#guard (layTrees [⟨2, some 4, none⟩, ⟨1, some 4, none⟩, ⟨2, some 4, none⟩, ⟨1, none, some 3⟩, ⟨3, none, some 3⟩, ⟨3, none, some 3⟩]).map (·.map (·.parts)) = some [[0, 2], [1, 3], [4, 5]]
#guard (layTrees [⟨7, none, some 5⟩]).map (·.map (Laid.depth [⟨7, none, some 5⟩])) = some [5]
#guard (numberTrees 3 [[⟨1, some 4, [0]⟩, ⟨2, none, [1]⟩], [⟨1, some 4, [0]⟩]]).map (·.map (·.1)) = some [3, 4, 5]
#guard (numberTrees (2 ^ 16 - 1) [[⟨1, some 4, [0]⟩]]).isSome = true ∧ (numberTrees (2 ^ 16) [[⟨1, some 4, [0]⟩]]).isSome = false
-- the page's known answers on places (at another edition than the one that
-- ships): a chain that continues the chain above and sends
-- (1, 4, -): the number 6; one that continues it, adopts a tree and then sends (1, 4, -): the
-- adopted tree's place 6, the new tree's number 7
#guard ((layTrees [⟨1, some 4, none⟩]).map fun l => takePlaces 6 [some l]) = some (some [[6]])
#guard ((layTrees [⟨1, some 4, none⟩]).map fun l => takePlaces 6 [none, some l]) = some (some [[6], [7]])
#guard (k7Chain.map fun l => takePlaces 0 (l.map some)) = some (some [[0, 1, 2], [3], [4, 5]])
#guard (takePlaces (2 ^ 16 - 1) [none]).isSome = true ∧ (takePlaces (2 ^ 16) [none]).isSome = false
#guard depthOK 48 = true ∧ depthOK 49 = false
-- R7.15: a tree of depth 2 under a list over [0, 16); at depth 4 the list comes back as it is (a
-- case of this library's own making)
#guard shortPosList 2 [1, 4, 7] = [0, 1, 3] ∧ shortPosList 2 [2, 6, 14] = [2] ∧ shortPosList 4 [2, 9, 14] = [2, 9, 14]
-- R7.7: the binding tree's vertices have a number of their own (the value is sections 2 and 3's known answer)
#guard hex (vertexB (pattern 32) (pattern 32) ((pattern 64).extract 32 64)) = "5060c36d8a53d1f4d4fcce8b2678190f7a3ab70d9a7e09c978a808fb3a01f408"

end Fmt
