-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/CarrierTyping.lean: builds the compiled verifier's proof input from a parsed file,
which this file's names and notes call a "carrier" (OnBytes/Maker/Carrier.lean decodes it).
Purpose. `toBPrfW` (OnBytes/Maker/TypingW.lean) builds that input (`OneProtocolProof`) from what the library's
own reader returns for a key file or a proof file. `File.toBPrf` is the same text with each value
taken from the parsed file instead, except two that come from the plan and are compared with the
parsed file's, and with one added check (`File.sealBare`). It calls no hash and reads no file.
States. No theorem: this is code to run. Call `File.toBPrfAt`: it returns the proof input, or `none`
for one of eight reasons, listed in the notes. `File.toBPrf` leaves out two of these checks
(`File.slotFits`, `File.treesFit`): it is for use in proofs, not for running. `File.key` is for
tests only.
Under. Besides the parsed file and the six parameters that fix the protocol and so the result's type
(`C`, `tF`, `tJ`, `t3`, `silent`, `run`), four inputs from the caller: the data D, the configuration
digest and the binding tree's shape, all three from the plan; and the plain parts of three rounds,
which the caller makes from the parsed file and which are no more trusted than it. The notes list
the caller's duties ("What a caller owes"); the first is that an error from `read` or a `none` here
means the answer no.
Does not show:
 1. that `Fmt.rootsOf` is safe on many roots: it uses a stack frame for each, and Lean's evaluator
    on its default stack ends the process at 11,000 in one round (compiled code was not tried);
    hence the check `File.sealBare`;
 2. that an honest file of the full size runs: `plainsT` uses a stack frame for each round, Lean's
    evaluator on its default stack ended the process between 9,500 and 12,000 rounds, and a chain of
    the full size has some 48,000;
 3. the limits of `leafSalt`: see "To be declared with every use" in Run/ParseBS.lean;
 4. that the format allows the binding tree's shape: 2 ^ depth is computed for any depth;
 5. anything about `root` and `copy`: this file does not read them;
 6. that the numbers given anywhere else for the binding tree (depth, salt length) are those of the
    shape given to `File.toBPrfAt`: that is the caller's duty, and nothing in the code enforces it;
 7. that `run1`, `run2`, `run3` are right: they are compared with nothing;
 8. the nonce of a round without proof of work: it is dropped unchecked, except in the first chain's
    last round;
 9. that an entry of `trees` with no row, a row at a leaf outside its tree or table, or a tree's row
    of the wrong width at a leaf that the verifier does not read is refused;
10. that `root`, `answers`, and in a proof file `copy`, are right: they are the parser's claim, and
    the caller must check them against the user's commitment ID;
11. that path digests which the joint pass over a pruned tree does not use are checked;
12. that lines 7 to 11 are complete or proved: they come from reading `read`, `File.toBPrfAt` and
    `verifyOneProtocol`, say nothing about another verifier, and assume a well-formed wire record;
13. a bound on memory: tables of about 200 times the file's size are built before a verifier can
    refuse, so bound the size of a stranger's file first;
14. a bound on time in `File.toBPrf` (entries times rounds): only `File.toBPrfAt` limits entries;
15. fast look-ups: each is linear, `verifyOneProtocol` makes one at every place of every tree and table, and
    rows at leaves outside a tree slow each one;
16. that the result is `toBPrfW`'s or `typeFile`'s for the original file: no theorem says so;
17. that an honest parsed file passes the checks here;
18. that the compiled verifier accepts the result;
19. any connection with a verifier's run: no definition here makes one, and the caller must give the
    same parsed file and data everywhere;
20. that the parser can be trusted: the result is a verifier's input like any other;
21. `typeFile`'s checks on the openings' shapes and the salts' exact lengths: not made here;
22. a column's width: a wrong one in a tree gives no opening; a stored column's is not looked at;
23. that the seeds belong to the table's name;
24. that `senderOf` agrees with the table of the plain data: `countsFit` is a check, not a theorem;
25. anything about soundness.

Notes in full, with every limit at length, are at the end of this file. They are the whole text.
Wherever this summary and the notes differ on a limit or a premise, the stronger limit holds, and
one that only one of the two names holds too; the notes hold for everything else.
Terms: lean/GLOSSARY.md.


-/
import OnBytes.Maker.Carrier
import OnBytes.Maker.TypingW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker.Carrier

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (opensApp ChainStr FileW)

/-- A round as `plainsT` and `rootsT` (OnBytes/Maker/TypingT.lean) read it. Of a round as read these
two take the items and the nonce alone; the other fields are laid empty. -/
def Round.out (x : Round) : _root_.Fmt.RoundOut :=
  ⟨ByteArray.empty, x.items, x.nonce, ⟨[], [], [], none⟩, [], []⟩

/-- A row of a table: the position; the column, the typed salt, the path. start: the carrier's run1,
run2 or run3, by the chain that sent the tree; the configuration's digest at the stored table. -/
def Row.row3 (start : ByteArray) (x : Row) : ℕ × Row3 :=
  (x.leaf, x.column, leafSalt start x.salt, x.path.map bytesToDig)

/-- The carrier's field for the run's value of chain 0 (run1), 1 (run2) or 2 (run3). Above 2: run3;
it is not called so. -/
def File.runOf (k : File) : ℕ → ByteArray
  | 0 => k.run1
  | 1 => k.run2
  | _ => k.run3

/-- The chain that sends the tree with the number j over the whole file, by the data: the first
chain's trees come first, then the shared chain's, then the second chain's (as in `WholeD.depth`,
OnBytes/Maker/Whole.lean). 2 also for a number beyond all trees; no look-up asks for such a tree. -/
def senderOf (D : WholeD) (j : ℕ) : ℕ :=
  if j < D.t₁ then 0 else if j - D.t₁ < D.t₂ then 1 else 2

/-- The number of the first tree whose chain in the carrier is not the data's; nothing if all
agree. -/
def File.chainOff (D : WholeD) (k : File) : Option ℕ :=
  (k.trees.find? fun t => t.chain != senderOf D t.tree).map fun t => t.tree

/-- The tables of all openings, keyed by the tree's number over the whole file. Which of the
carrier's run1, run2, run3 begins a leaf's typed salt is taken from the data, not from the carrier's
`chain`. The value itself is the carrier's and is compared with nothing. -/
def File.tabs (D : WholeD) (k : File) : List (ℕ × List (ℕ × Row3)) :=
  k.trees.map fun t => (t.tree, t.rows.map (Row.row3 (k.runOf (senderOf D t.tree))))

/-- The stored table as the protocol's blocks read it (`TableKey`, OnBytes/Iop/Foldeq.lean), of the
carrier's answers and the seeds in the file beside it, under the statement's item 0; no hash call.
For tests alone (the head of this file): a verifier draws the seeds itself.
s: the table's shape, from the plan. Nothing if the numbers of answers, of seeds or of a seed's
coordinates are not the shape's (`TableKey.fits`). -/
def File.key (k : File) (seeds : List (List _root_.Fmt.Ext × _root_.Fmt.Ext))
    (s : Params.IndexShape) : Option TableKey :=
  let key : TableKey := ⟨0, (k.answers.map E.ofTriple).toArray,
    seeds.map fun x => ⟨x.1.map E.ofTriple, E.ofTriple x.2⟩⟩
  if key.fits s then some key else none

/-- The seal is there and is bare: the first chain has a last round, and it has no item and the
nonce 0. Why it is asked: the head of this file. -/
def File.sealBare (k : File) : Bool :=
  match k.rounds1.getLast? with
  | some r => r.items.isEmpty && r.nonce == 0
  | none => false

/-- The carrier's fields on the binding tree against the tree's shape s, from the plan: the leaf's
salt has the shape's number of bytes, there is one sibling for each level, the number of places is
2 ^ the depth, and the place is below it. Where the chain joins, the compiled verifier does not test
the length of `rsalt` (the head of OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), so the salt's length is
tested here. In a carrier that was read the number of places is a u64: so a shape that fits has a
depth of at most 63, and places + place, which `File.toBPrf` lays as one word, is below 2 ^ 64. It
is not asked that the format admits the shape (`Proof.bindingOk`, OnBytes/Proof/Place.lean). -/
def File.slotFits (s : Params.LinBindingShape) (k : File) : Bool :=
  k.slotSalt.size == s.saltBytes && k.slotPath.length == s.logLeaves &&
    k.places == 2 ^ s.logLeaves && decide (k.place < k.places)

/-- The number of all trees that the three chains send, by the data. -/
def treesIn (D : WholeD) : ℕ := D.t₁ + D.t₂ + (D.ds₃.map (·.trees.length)).sum

/-- Every entry of trees has the number of a tree that the data know. The number of all trees is
computed once. In a carrier that was read the numbers rise strictly, so there are then at most as
many entries as trees. Why it is asked: "Cost" in the head of this file. -/
def File.treesFit (D : WholeD) (k : File) : Bool :=
  let n := treesIn D
  k.trees.all fun t => decide (t.tree < n)

section
variable {TF TJ T3 Xi : Type} (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **The proof string of a carrier.** cfg: the configuration's digest. places: the number of the
binding tree's leaves, from the plan. pF, pJ, p3: the plain parts of the three silent rounds. The
first stretch is the first chain without its last round, the seal, as in `toBPrfW`. Nothing also
where the seal is not bare (`File.sealBare`), the carrier's number of places is not `places`, or a
tree's chain in the carrier is not the data's (the caller can ask `File.chainOff` for the tree).
The roots are walked in the arm behind all six tests. Not tested: the length of the salt in the
binding tree, the number of siblings, that the place is below the number of places, that an entry's
tree is one of the data's, the length of cfg. Whoever runs a verifier on the string calls
`File.toBPrfAt`. -/
def File.toBPrf (k : File) (cfg : ByteArray) (places : ℕ) (pF : TF) (pJ : TJ) (p3 : T3) :
    Option (OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) :=
  match k.sealBare, k.places == places, k.chainOff D,
      plainsT C D.ds₁ (k.rounds1.map Round.out).dropLast,
      plainsT C D.ds₂ (k.rounds2.map Round.out), plainsT C D.ds₃ (k.rounds3.map Round.out) with
  | true, true, none, some pl₁, some pl₂, some pl₃ =>
    let tabs := k.tabs D
    let tab := k.stored.map (Row.row3 cfg)
    let k₁ := str₁ C D tF tJ t3 pF pl₁ tabs (k.rounds1.map Round.out)
    let k₂ := str₂ C D tF tJ t3 pJ pl₂ tabs (k.rounds2.map Round.out)
    let k₃ := str₃ C D tF tJ t3 p3 pl₃ tabs (k.rounds3.map Round.out)
    some
      { salt := bytesToBits k.run1
        roots := k₁.roots ++ (k₂.roots ++ k₃.roots)
        plains := Plains.app (s := (chainsOf C D tF tJ t3).c₁)
          (t := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) k₁.plains
          (Plains.app (s := (chainsOf C D tF tJ t3).c₂) (t := (chainsOf C D tF tJ t3).c₃)
            k₂.plains k₃.plains)
        opens := opensApp (s := (chainsOf C D tF tJ t3).c₁)
          (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) k₁.opens
          (opensApp (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
            k₂.opens k₃.opens)
        ext := fun p => atT (fun c => some (p.val, c)) tab p.val
        rtreq := bytesToDig k.bindRoot
        slot := k.place
        path := k.slotPath.map bytesToDig
        rsalt := rsOf (places + k.place) k.slotSalt }
  | _, _, _, _, _, _ => none

/-- **The proof string of a carrier, at the binding tree's shape from the plan: the form to call.**
Nothing unless the carrier's four fields on the binding tree fit the shape s (`File.slotFits`) and
every entry of trees has the number of a tree of the data (`File.treesFit`); else `File.toBPrf` at
the shape's number of leaves. Both tests are made before `File.toBPrf` is called. -/
def File.toBPrfAt (k : File) (cfg : ByteArray) (s : Params.LinBindingShape) (pF : TF) (pJ : TJ)
    (p3 : T3) : Option (OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) :=
  if k.slotFits s && k.treesFit D then
    k.toBPrf C D tF tJ t3 silent run cfg (2 ^ s.logLeaves) pF pJ p3
  else none

end

end OnBytes.Maker.Carrier

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/CarrierTyping.lean: from a carrier (OnBytes/Maker/Carrier.lean) to the proof string of
the one joined protocol that OnBytes/Maker/Whole.lean makes of a key file or a proof file.

Why. `toBPrfW` (OnBytes/Maker/TypingW.lean) lays that proof string of what the program's reader
returns for a file's three chains. Of that reading it takes the first chain's run's value, of each
round its items and its nonce, and of the binding tree the root, the place and the number of leaves;
beside it the tables of all openings, the stored table's openings, and the salt and the siblings of
the leaf in the binding tree. A carrier holds all of these. `File.toBPrf` is the text of `toBPrfW`
with each taken from the carrier, but for two that the plan knows: the number of the binding tree's
leaves (the caller gives it) and which chain sent a tree (from the data D). The carrier's word on
these two is held against them: a difference gives nothing. It calls no hash and reads no file. Code
to be run; no theorem is stated.

One test has no twin in `toBPrfW`: the first chain's last round, the seal, must be there, with no
item and the nonce 0 (`File.sealBare`). Both texts drop that round before the plain parts are typed,
and both still walk it for roots. On the road of `toBPrfW` the plan says how many items are read for
a round. In a carrier nothing else would hold the seal's items, and the walk for roots
(`Fmt.rootsOf`, Fmt/Rules8.lean) takes one stack frame for each root. In Lean's evaluator, under its
default stack, that walk returns at one round of 10,000 roots and ends the process at 11,000 ("deep
recursion"), which is no refusal; compiled code was not tried. So the seal is held before it is
walked. That a seal has no item and asks for no proof of work is a test on the plan (`Whole.fits`,
clause 6, OnBytes/Three/Data.lean). All other rounds are held item by item to the data's lists
(`PlainOf.ofGots`, Run/PlanQTypes.lean) before any is walked.

A second walk goes by stack frames, at an honest carrier too, and in `toBPrfW` as well: the typing
of the plain parts (`plainsT`, OnBytes/Maker/TypingT.lean) takes one frame for each round of the
plan. In the evaluator, under its default stack, it returns at a chain of 3,677 rounds and ends the
process somewhere between 9,500 and 12,000. A chain of the full size has some 48,000 rounds
(OnBytes/Three/Data.lean). There the laying needs a larger stack (the flag `--tstack` of `lean`) or
compiled code; neither has been tried at this walk. That is a limit on honest files, and no refusal.

Main definitions.
  `Round.out`: a carrier's round as the typing of the plain parts reads a round.
  `Row.row3`, `File.tabs`: the tables of the openings. A leaf's typed salt is the carrier's run1,
    run2 or run3, by the chain that sent the tree, then the file's salt (`leafSalt`; limits: "To be
    declared with every use" in the head of Run/ParseBS.lean); at the stored table the
    configuration's digest is in the run's value's place.
  `senderOf`, `File.chainOff`: which chain sent a tree, by the data; the first tree at which the
    carrier says otherwise.
  `File.key`: a key of the stored table with no hash call, made of the carrier's answers and a seeds
    file. It is for tests: the dry runs that give the data can be run at it, and drawn seeds can be
    compared with it. A verifier draws the seeds itself. Of a key the dry runs read the sizes alone:
    at every key with item 0 that fits the shape they state the same rounds (`keyAlike_of_fits`,
    `dryKey_keyAlike`, `dryProof_keyAlike`, OnBytes/Maker/FilesFree.lean), so
    no value of the carrier enters the data through the key.
  `File.sealBare`: the test on the seal.
  `File.toBPrf`: the proof string. It returns nothing for six causes, and the caller can ask each
    by itself: the seal is not bare; the carrier's number of places is not the caller's; a tree's
    chain in the carrier is not the data's (`File.chainOff`); the plain parts of the first, the
    second or the third stretch do not type (`plainsT`, OnBytes/Maker/TypingT.lean). Of the binding
    tree it tests the number of places alone: it is there for equations, not for a run.
  `File.slotFits`, `File.treesFit`, `File.toBPrfAt`: the form to call: `File.toBPrf` behind two more
    tests, a seventh and an eighth cause: the carrier's four fields on the binding tree fit that
    tree's shape, from the plan; every entry of trees has the number of a tree that the data know.

What the caller gives. Public or the user's, and not in a carrier: the data D of the file's shape;
the configuration's digest; the binding tree's shape (its number of leaves is hashed, and 2 ^ its
depth is computed here, whatever the depth: the program's reader of a place asks a depth of at most
48 first, `Proof.bindingOk`, OnBytes/Proof/Place.lean). Made by the caller of the carrier's answers,
copy, run2 and run3, and so no more trusted than the carrier: the plain parts of the three silent
rounds. Not read in this file: the carrier's root and copy.

What a caller owes. Where `read` refuses or `File.toBPrfAt` returns nothing, the answer is no. The
stored table's root is the first of the external roots that the verifier is given. `File.toBPrf`
itself lays neither that root nor the answers nor the copy; the answers and the copy come into the
string through the silent rounds' plain parts, which the caller makes. If the three are taken from
the carrier they are the parser's word, and they are held to the user's commitment ID. At a proof
file root and answers are the leaf table's, which the ID reaches through the leaf file alone; that
file's parsed form holds the same pair, and a caller takes the pair from one place or compares the
two. The joining round's and the seam's plain parts are made of the same carrier's run2 and run3.
The data, the digest, the shape and the verifier's own numbers come from the plan. Every number that
a verifier, a page or a guard is given for the binding tree is that of the one shape that
`File.toBPrfAt` is given: the depth is its logLeaves, the number of bytes of the leaf's salt its
saltBytes. No term here makes these letters one.

What no check sees of a carrier, by reading `read`, `File.toBPrfAt` and `verifyOneProtocol`
(OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean); of another verifier the list says nothing. Beyond the
tests of the form, which `read` makes on every field, these three neither refuse nor check the
following.
  `run1`, `run2`, `run3`. They are compared with nothing: run1 is laid as the string's salt, and
    each of the three as the first 256 bits of the typed salt of every leaf of its chain's trees,
    where the verifier tests the length alone. Which chain's value stands there is the data's word;
    the value is the carrier's.
  The nonce of a round without proof of work, but for the first chain's seal's: it is dropped as
    the string is laid (`GPlain.mk`, Iop/Grind.lean). The shared chain ends in a seal too: that
    round is typed like any other, and its nonce is dropped like any other.
  An entry of trees without a row; a row at a leaf that is no position of its tree (2 ^ depth or
    more; at the stored table 2 ^ D.a or more); at a leaf that the verifier does not read, a tree's
    row whose column has not the tree's width.
  `root`, `answers`, and at a proof file `copy`: they are the caller's to use and to check.
  The digests of a path that the joint walk of a pruned tree does not use (the head of
    Verifier.lean, "Limits", (iii)).
The first and the last are part of the proof string. The others are not, but for what the caller
lays of answers and copy. Seen and refused, and so not in this list: any other row at a position
that the verifier does not read. It is an opening where nothing is read, which the strict format
does not allow (`strictComp`, Verifier.lean; `strictExt`, Compile/Bcs.lean); these tests reach every
position if the wire record is well-formed (that head, "Limits").

Cost. The tables are laid whole as the string is laid, before a verifier can say no. A row's typed
salt is a list of bits, 256 for its start and 8 for each byte of the file's salt, laid anew for each
row, and a row takes as little as 32 bytes in a carrier. At 24 bytes for a list's cell that is about
200 times the carrier's size. Rows that no look-up reaches are laid like the others, and the
carrier's size alone bounds their number: whoever reads a stranger's carrier bounds its size first.
`senderOf` walks the data's rounds anew at each call, so `File.chainOff` and `File.tabs` take the
number of entries times the number of rounds. `File.toBPrfAt` holds the entries to the data's trees
first (`File.treesFit`, with the number of all trees computed once); `File.toBPrf` does not. A
look-up in a list is linear in its length, and `verifyOneProtocol` looks up at each of the 2 ^ depth places
of each tree and at each of the 2 ^ D.a places of the stored table, and again at each position that
is read: rows at leaves that are no positions lengthen each of these.

Not claimed. That `File.toBPrf` at a carrier made of a file is `toBPrfW` at the reading of that
file, or `typeFile`'s string: no theorem says it. That an honest carrier passes the tests here. That
the compiled verifier accepts this string. No definition here joins the laying with a verifier's
run: a caller writes that itself, and gives the same carrier and the same data at every place. The
parser that wrote the carrier is not trusted: it can be read as the prover's last step, and this
string is a verifier's input like any other. The tests that `typeFile` (OnBytes/Maker/TypeFile.lean)
makes on the openings' shapes and on the leaves' salts' exact lengths are not made here, and nothing
here rests on the parser having made them; that no tree and no leaf comes twice is the reader's test
(`read`). A tree's column of another width than the tree's gives no opening at that position (at a
position that the verifier reads that is its no); a stored column's width is not looked at. That the
seeds are those of the table's name. That `senderOf` is the chain in the table of the plain data:
there the row at the number of the n-th tree of chain c has the chain c (`table_chain`,
OnBytes/Maker/TableChain.lean), and that D counts the trees as that table does is a test
(`countsFit`, OnBytes/Maker/WholeOf.lean), not a law. Nothing on soundness.

Terms: lean/GLOSSARY.md; "carrier" is explained in the head of OnBytes/Maker/Carrier.lean.
-/
