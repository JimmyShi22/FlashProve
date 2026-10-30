-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M1View.lean: from what the strict reader hands out to the view on which a decision is written,
and the verifier on bytes that the two make.

The strict reader (wholeChain, Fmt/Rules8.lean) is this library's rendering of the verifier of the
format page (docs/format/FORMAT.md, which comes with the programs, that is, with the C++
implementation that accompanies this Lean code; this file is not held against the page as it
ships, and may differ from it) up to its decision: it cuts the file,
recomputes the hash chain from which the challenges are drawn, tests spellings, the proof of work
and the listed positions, checks every Merkle opening against its root, refuses two different values
at one vertex under one root, and requires that no byte is left over (these are the main checks, not
every check of form).
Fmt/View.lean is the record on which a protocol's decision is written:
dec : statement → View → Bool. This file joins the two.

Sources. The format page; this file is not held against it as it ships, and may differ.
No rule of the page is rendered here; the rules are rendered in Fmt/Rules8.lean. No Mathlib is
imported.

1. What the file contains.
   `noRoots`: A message's items without its roots.
   `openedOf first r`: The opened columns of one round, as described under viewOf.
   `viewOf first o`: The view of a chain that was read. Its rounds: for each round the items without
      the roots, and what was drawn. Its opened columns: for each opening, in the order of the
      rounds and within a round in the order of the file, and for each position of its list, in
      increasing order: (the tree's number less "first", the position, the column). "first" is the
      number of the chain's first own tree (`Spec.firstTree`; 0 for a chain that follows no other).
      So an own tree is named by its place in the order of sending, from 0, as Fmt/View.lean asks.
   `verifyW h S dec y file : m Bool`: The verifier on bytes, over any monad, with the hash as its
      first argument: read the whole file; refuse if the reader refuses; else decide on the view.
   `verify`: The same at the identity monad and the format's hash.
   `M1ViewToy.dec`: The decision of a small toy of this library's own (Fmt/Toy1.lean), written on
      the view: for the tests.
   A limit. A tree that is given from outside (a stored tree, a tree of another chain) is also named
   in the view by its own number less "first" (cut off at 0). A decision that reads such trees
   cannot tell them from own trees by the view alone. The chains for which this file is meant have
   none; for chains that open stored tables see Fmt/Rules8X.lean (viewX).

2. What is checked when the file compiles (tests, #guard). At the format page's own known answer for
a chain in a file (second field; the file stands in Fmt/Rules8.lean): three rounds; the root is not
among the items; the opened columns stand under tree 0 at the positions of its list; the drawn
positions are handed on as drawn, repeats kept. At a small toy of this library's own (Fmt/Toy1.lean,
Fmt/Toy1Files.lean; 21 files): both honest files are accepted and every altered copy is refused, and
the verdicts are those of that toy's own verifier, file by file. At a made-up chain of
Fmt/Rules8More.lean whose first own tree has the number 3: its trees are 0 and 1 in the view (a
stored tree with the number 0 is cut off at 0: the limit named above).

3. Theorems. No theorem in this file. A test (#guard) is an evaluation made while the file compiles;
the compile fails if the result moves; it leaves no theorem.

4. What is not claimed. That this view is the one that the generic construction makes from a typed
transcript (viewOf, Run/PlanQTypes.lean) is tested nowhere in this file. Which decision belongs to
which protocol is not said here.

Terms: lean/GLOSSARY.md.
-/
import Fmt.View
import Fmt.Toy1
import Fmt.Rules8More

namespace Fmt

/-- a message's items without its roots -/
def noRoots : List ItemValue → List ItemValue
  | [] => []
  | .root _ :: l => noRoots l
  | x :: l => x :: noRoots l

/-- the opened columns of one round -/
def openedOf (first : Nat) (r : RoundOut) : List (Nat × Nat × List UInt64) :=
  r.opens.flatMap fun x => (x.2.1.zip x.2.2.cols).map fun p => (x.1.tree - first, p.1, p.2)

/-- The view of a chain that was read. -/
def viewOf (first : Nat) (o : ChainOut) : View where
  rounds := o.rounds.toList.map fun r => ⟨noRoots r.vals, r.drawn⟩
  opened := o.rounds.toList.flatMap (openedOf first)

/-- The verifier on bytes: the reader, then the decision. -/
def verifyW {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
    {Y : Type} (S : Spec) (dec : Y → View → Bool) (y : Y) (file : ByteArray) : m Bool := do
  match ← wholeChain h S file with
  | none => pure false
  | some o => pure (dec y (viewOf S.firstTree o))

def verify {Y : Type} (S : Spec) (dec : Y → View → Bool) (y : Y) (file : ByteArray) : Bool :=
  verifyW (m := Id) formatHash S dec y file

/-! ## Tests (#guard) -/

-- the page's known answer of a chain in a file, field 2: three rounds; the root is not among the
-- items; the opened columns under tree 0 at the positions of its list
open Known8 in
#guard ((read .two file2).map fun o => ((viewOf 0 o).rounds.map (·.vals), (viewOf 0 o).opened)) ==
  some ([[], [.answer (9, 9, 9)], [.e (4, 5, 6)]], [(0, 1, [101, 201, 301]), (0, 5, [105, 205, 301]), (0, 6, [106, 206, 300])])
-- what was drawn is handed on as it is: the positions as drawn, repeats kept
open Known8 in
#guard ((read .two file2).map fun o => (viewOf 0 o).rounds.map (·.drawn.poss)) == some [[], [], [1, 5, 6, 5]]

namespace M1ViewToy

/-- the decision of the small toy of this library's own (Fmt/Toy1.lean), on the view: the last
round's one item is the claim plus the sum of the opened columns, coordinate by coordinate modulo
the prime -/
def dec (c : Ext) (v : View) : Bool :=
  let p := Fld.two.p
  let s := v.opened.foldl
    (fun (a : Nat × Nat × Nat) x =>
      ((a.1 + (x.2.2.getD 0 0).toNat) % p,
        (a.2.1 + (x.2.2.getD 1 0).toNat) % p,
        (a.2.2 + (x.2.2.getD 2 0).toNat) % p))
    (c.1.toNat, c.2.1.toNat, c.2.2.toNat)
  match (v.rounds.getLast?.map fun (r : RoundView) => r.vals : Option (List ItemValue)) with
  | some [ItemValue.e x] => x.1.toNat == s.1 && x.2.1.toNat == s.2.1 && x.2.2.toNat == s.2.2
  | _ => false

end M1ViewToy

-- the small toy of this library's own (Fmt/Toy1.lean) through `verify`: both honest files accepted;
-- every altered copy refused; the verdicts are those of the toy's own verifier, file by file
#guard Toy1.files.all fun x => verify (Toy1.spec Toy1.claim) M1ViewToy.dec Toy1.claim x.2.1 == x.2.2.isNone
#guard Toy1.files.all fun x => verify (Toy1.spec Toy1.claim) M1ViewToy.dec Toy1.claim x.2.1 == Toy1.verify Toy1.claim x.2.1
#guard Toy1.files.length = 21

-- a chain whose first own tree has the number 3: in the view its trees are 0 and 1 (the stored
-- tree, number 0, is cut off at 0: the limit that the head names)
open Toy8M in
#guard ((read good .inFile (honest good)).map fun o => ((viewOf 3 o).opened.map (·.1)).eraseDups) == some [0, 1]

end Fmt
