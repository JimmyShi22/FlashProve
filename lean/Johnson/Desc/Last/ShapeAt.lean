-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeAt.lean: THE LAST CHAIN's BOOK-KEEPING AS A TEST WITH CODE: a filling of the
letters of the promise of the table of the last chain's joints (`PromMeaningL`,
Johnson/Desc/Last/BordersLast.lean): `shape k`, k = 0 … 4, and `nothingLeft`. Definitions with code;
no theorem. The laws: Johnson/Desc/Last/ShapeGives.lean; the tie to the table and the tries:
Johnson/Desc/Last/ShapeAtTable.lean; the rows: Johnson/Desc/Last/ShapeRows.lean.
`start₃E` TAKES THE NUMBERS OF W, OF THE OWN GROUP AND OF THE MASK BY NAME (ten arguments):
`Handed` is `FirstEnd₃`.

Why. Every joining of the last chain's four rows takes the table's promise as a letter and says "no
member". Premises that are not tried at a filling can be empty, and some of them are (said here
without a theorem). Here the letter is a closed term on the records of
Johnson/Desc/Third/State.lean, so that each row's named premise can be had from its yes, or be seen
to be no test on public records; so that the step from border to border can be stated; and so that a
ride can evaluate it.
This file does not list the members and rows that must agree with what was handed: AT BORDER
0 IT PINS THE WHOLE RECORD; AT BORDERS 1 AND 2 ALL OF IT BUT FOUR FIELDS OF ONE TREE: the statement,
the named values, the roots, every place of the book and every older tree are fixed by what was
handed; of the one new tree (Omega's) the number and the source are; its shape, its parts (but that
Omega is part 0: "the book fits"), and its two marks on lists are free.

The design, border by border. s₀ := what `start₃E` returns of what was handed.
  at every border: the start returns a record; `handedClauses`: seven tests on what was handed
    alone; `memberClauses`: the own group that was handed has two members, each with one sample row;
    Omega has one at the shared chain's end.
  0: THE RECORD IS s₀ (`decide (s = s₀)`, Johnson/Desc/Third/Eq.lean); the own group's open rows
    name messages of the statement alone; it has an open row; the mask has come.
  1, 2: THE RECORD IS ONE THAT K14's SECOND PART LAYS FROM s₀: `Laid`
    (Johnson/Desc/Third/Law/LaidDef.lean), field by field, each clause under its field's name; the
    statement is tidy; the book fits; the mask has come. At 2 beside: what the block "the taken
    trees' sources" asks.
  3, 4: the own group's test has begun; the named values are those behind K14's second part; the
    codes are the first chain's; the statement is tidy.

Main names (namespace `VerifiableInference.Desc.Last`).
  `Handed` := `FirstEnd₃` (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean): the seven things of the first chain's
    last record. `namesB`, `tiedB`. Others' tests that it calls: `Means.tidy4B`
    (Johnson/Desc/Means/TestsBack.lean: it says yes just where `Means.Tidy` holds), `Means.rowInB`
    (Johnson/Desc/Means/TestsB.lean), `bookFitsB`, `tenantB` (Johnson/Desc/Sound/BookTests.lean).
  `handedClauses p h o`, `memberClauses s₀ o`, `laidClauses S s s'` | `laidB`, `clausesAt p
    ownRounds k s₀ s`, `allClauses`: lists of (name, Bool). **`shapeAt p ownRounds k h o s`**: all
    of `allClauses`.
  **`fillAt p ownRounds hand ended : PromMeaningL S₂ S₃ P₁`**, hand : P₁ → Option Handed, ended : S₂
    → Option SharedOut: where either gives nothing, shape says no; nothingLeft := all of
    `ChainEnd.untestedL` (Johnson/Desc/ChainEnd.lean): what the chain's last block asks; `fin₃` asks
    less.

WHO READS EACH LETTER. p (the codes, the plan's shape of the test on the table): the start, (Dot)'s
making, Omega's shape. ownRounds (the own test's declared rounds): border 2's last clause alone.
hand, ended (how what was handed and the shared chain's end are read off the table's two records):
`fillAt` alone.
WHAT CANNOT STAND IN shape, BY ITS TYPE (it reads what was handed, the shared chain's last record
and the chain's own record): whatever reads the prover's strings ("held, shown, no collision" of a
member; an equation between a member's word and a kind's own term for it; the batching's converse)
or the witness (what a pin says). These belong to the table's letter Oc and to the rows' laws.
Limits. (1) NO MEMBER: it is evaluated at no record in this library. (2) "The mask has come" says no
at a shape whose masks are not sent ahead (there the start lays no mask): the promise is empty at
such a shape. (Every shape that the planner's sizing returns sends them ahead:
Johnson/Desc/Last/ShapeMask.lean.) (3) Borders 1 and 2 part in one clause; 3 and 4 in none (the
blocks between turn no record). (4) At 3 and 4 nothing is said of the book, the members or the rows.
(5) Each clause says no where the thing of which it speaks is absent, BUT `tenantB`, which says yes
where Omega has no place in the shared chain's book. (6) hand and ended are letters: nothing says
that they read the right fields. (7) The cost: `Means.tidy4B` and the comparisons walk whole
records; how long that takes at the full size is not known. (8) IT HOLDS AT PLANS WITH ONE ANSWER TO
A SAMPLE ALONE: "one sample row" (three clauses on the members and on Omega) says no at a setting
with more than one answer to a sample, since a message has as many sample rows as its shape has
answers: the promise is empty there. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Third.Eq
import Johnson.Desc.Third.TakenSources
import Johnson.Desc.ChainEnd
import Johnson.Desc.Third.Law.LaidDef
import Johnson.Desc.Means.TestsBack
import Johnson.Desc.Sound.BookTests
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third
open VerifiableInference.Desc.Sound (bookFitsB tenantB)

/-- What is handed of the first chain's last record: its statement, its book, the roots received,
the numbers of W, of the own group and of the mask as that chain's own record names them, the list
of pending rows: `FirstEnd₃` (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean), which `firstOfS`
(Johnson/Desc/Third/Border.lean) makes. -/
abbrev Handed : Type := FirstEnd₃

/-! ## 1 Small tests -/

/-- The own group's open rows name messages of the statement alone. -/
def namesB (s : S₃) : Bool :=
  match s.st.groups[s.loc.own]? with
  | some G => G.rows.toList.all fun r => r.oracles.all fun o => decide (o < s.st.oracles.size)
  | none => false

/-- What the block "the taken trees' sources" asks (Johnson/Desc/Third/TakenSources.lean), of the
own test's declared rounds. -/
def tiedB (ownRounds : List Fmt.DeclaredRound) (s : S₃) : Bool :=
  match takenOf s with
  | some ts =>
    (ts.all fun x => opensTaken ownRounds x.1 x.2) &&
      (ownRounds.flatMap (·.opens)).all fun o =>
        match o.2 with
        | .own _ => true
        | .taken c n => ts.contains (c, n)
  | none => false

/-! ## 2 What was handed -/

/-- **The clauses on what was handed alone**, each with its name. h: of the first chain's last
record; o: of the shared chain's end. -/
def handedClauses (p : P₁₄) (h : Handed) (o : SharedOut) : List (String × Bool) :=
  [("the first chain's last statement is tidy", Means.tidy4B h.st),
   ("the shared chain's last statement is in order", Means.inOrderB o.st),
   ("the first chain's book fits", bookFitsB h.book),
   ("the shared chain's book fits", bookFitsB o.book),
   ("in the shared chain's book Omega is part 0 of its tree", tenantB o),
   ("Omega is there at the shared chain's end, with the plan's shape",
      match o.st.oracles[o.omega]? with
      | some y => decide (y.shape = p.S.omega)
      | none => false),
   ("one pending row, and its row weights are lawful",
      match h.pending with
      | [r] => r.g.all (·.ok)
      | _ => false)]

/-- **The clauses on the own group as it was handed**, read at the start's record s₀, and on Omega
at the shared chain's end: how many members, how many sample rows. -/
def memberClauses (s₀ : S₃) (o : SharedOut) : List (String × Bool) :=
  [("the own group that was handed has two members",
      match s₀.st.groups[s₀.loc.own]? with
      | some G => G.members.size == 2
      | none => false),
   ("each of the two has one sample row",
      match s₀.st.groups[s₀.loc.own]? with
      | some G => G.members.toList.all fun i =>
          match s₀.st.oracles[i]? with
          | some x => x.sampleRows.size == 1
          | none => false
      | none => false),
   ("Omega has one sample row at the shared chain's end",
      match o.st.oracles[o.omega]? with
      | some y => y.sampleRows.size == 1
      | none => false)]

/-! ## 3 What K14's second part has laid, as a test -/

/-- The own group behind the block. -/
def groupBehind (s : S₃) (G : OnBytes.Group) (dot : OnBytes.Row) : OnBytes.Group :=
  { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
      s.st.oracles.size
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false
    rows := G.rows.push dot }

/-- **The clauses of `Laid`** (Johnson/Desc/Third/Law/LaidDef.lean), each under its field's name. s:
the record in front; s': the record behind. -/
def laidClauses (S : Params.LinShape) (s s' : S₃) : List (String × Bool) :=
  match s.loc.border with
  | none => [("border", false)]
  | some b =>
    match b.shared.st.oracles[b.shared.omega]?, s.st.groups[s.loc.own]?,
      linDotRow S b.g b.shared.psi s.st.oracles.size (linLayOmega s.st.codes S) s.loc.w
        (linLayW s.st.codes S) with
    | some y, some G, some dot =>
      [("loc", decide (s'.loc = { s.loc with border := none, omega := s.st.oracles.size })),
       ("sampled", y.sampled),
       ("size", decide (s'.st.oracles.size = s.st.oracles.size + 1)),
       ("copy", decide (s'.st.oracles[s.st.oracles.size]? = some
          { shape := y.shape, sampled := true
            sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size), pad := y.pad
            groups := [s.loc.own] })),
       ("notBegun", !G.inRun),
       ("plain", decide (dot.kind = .plain)),
       ("group'", decide (s'.st.groups[s.loc.own]? = some (groupBehind s G dot))),
       ("dotIn", Means.rowInB s'.st (groupBehind s G dot) dot),
       ("codes", decide (s'.st.codes = s.st.codes)),
       ("old", (List.range s.st.oracles.size).all fun i =>
          decide (s'.st.oracles[i]? = s.st.oracles[i]?)),
       ("oldGroups", (List.range s.st.groups.size).all fun i =>
          i == s.loc.own || decide (s'.st.groups[i]? = s.st.groups[i]?)),
       ("groups", decide (s'.st.groups.size = s.st.groups.size)),
       ("roots", decide (s'.roots = s.roots)),
       ("trees", decide (s'.book.trees.size = s.book.trees.size + 1)),
       ("step", decide (s.st.oracles.size = s.book.place.size)),
       ("place", decide (s'.book.place[s.st.oracles.size]? = some (s.book.trees.size, 0))),
       ("oldPlaces", (List.range s.book.place.size).all fun i =>
          decide (s'.book.place[i]? = s.book.place[i]?)),
       ("places", decide (s'.book.place.size = s.book.place.size + 1)),
       ("oldTrees", (List.range s.book.trees.size).all fun i =>
          decide (s'.book.trees[i]? = s.book.trees[i]?)),
       ("tree",
          match b.shared.book.place[b.shared.omega]? with
          | some q =>
            (match b.shared.book.trees[q.1]?, s'.book.trees[s.book.trees.size]? with
              | some t, some tO =>
                decide (t.parts.size = 1) && decide (tO.number = t.number) &&
                  decide (tO.src = t.src)
              | _, _ => false)
          | none => false),
       ("order", !Means.inOrderB s.st || !Means.inOrderB b.shared.st || Means.inOrderB s'.st)]
    | _, _, _ => [("there, group, dotIs", false)]

def laidB (S : Params.LinShape) (s s' : S₃) : Bool := (laidClauses S s s').all (·.2)

/-! ## 4 The book-keeping at a border -/

/-- **The clauses at border k**, each with its name. s₀: the start's record of what was handed. -/
def clausesAt (p : P₁₄) (ownRounds : List Fmt.DeclaredRound) (k : Nat) (s₀ s : S₃) :
    List (String × Bool) :=
  match k with
  | 0 =>
    [("the record is the start's of what was handed", decide (s = s₀)),
     ("the own group's open rows name messages of the statement alone", namesB s),
     ("the own group has an open row",
        match s.st.groups[s.loc.own]? with
        | some G => !G.rows.isEmpty
        | none => false),
     ("the mask has come", s.loc.mask.isSome)]
  | 1 | 2 =>
    laidClauses p.S s₀ s ++
    [("the statement is tidy", Means.tidy4B s.st),
     ("the book fits", bookFitsB s.book),
     ("the mask has come", s.loc.mask.isSome)] ++
    (if k == 2 then [("what the taken trees' sources' block asks", tiedB ownRounds s)] else [])
  | _ =>
    [("the own group's test has begun",
        match s.st.groups[s.loc.own]? with
        | some G => G.inRun
        | none => false),
     ("the named values are those behind K14's second part",
        decide (s.loc = { s₀.loc with border := none, omega := s₀.st.oracles.size })),
     ("the codes are the first chain's", decide (s.st.codes = s₀.st.codes)),
     ("the statement is tidy", Means.tidy4B s.st)]

/-- **THE BOOK-KEEPING AT BORDER k: A TEST WITH CODE ON PUBLIC RECORDS ALONE.** -/
def allClauses (p : P₁₄) (ownRounds : List Fmt.DeclaredRound) (k : Nat) (h : Handed) (o : SharedOut)
    (s : S₃) : List (String × Bool) :=
  match start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o with
  | .ok s₀ => handedClauses p h o ++ memberClauses s₀ o ++ clausesAt p ownRounds k s₀ s
  | .error _ => [("the start returns a record of what was handed", false)]

def shapeAt (p : P₁₄) (ownRounds : List Fmt.DeclaredRound) (k : Nat) (h : Handed) (o : SharedOut)
    (s : S₃) : Bool :=
  (allClauses p ownRounds k h o s).all (·.2)

/-- **THE FILLING OF THE TABLE's LETTERS OF THE PROMISE.** hand, ended: how what was handed, and
the shared chain's end, are read off the table's two records: letters. Where nothing is
handed (`firstOfS`, Johnson/Desc/Third/Border.lean, can return nothing), or the shared chain has not
ended: no. -/
def fillAt {S₂ P₁ : Type} (p : P₁₄) (ownRounds : List Fmt.DeclaredRound) (hand : P₁ → Option Handed)
    (ended : S₂ → Option SharedOut) : PromMeaningL S₂ S₃ P₁ where
  shape := fun k x e s =>
    match hand x, ended e with
    | some h, some o => shapeAt p ownRounds k h o s
    | _, _ => false
  nothingLeft := fun s => (ChainEnd.untestedL s.st).all (·.2)

end VerifiableInference.Desc.Last
