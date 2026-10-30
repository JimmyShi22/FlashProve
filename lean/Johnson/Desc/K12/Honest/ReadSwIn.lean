-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/ReadSwIn.lean: the field `read` of what a code switch's acceptance asks
(`SwitchFront`, Johnson/Prover/Link/FormSwitch.lean) is derived, at a list of trees, from `ReadAsks`
(Johnson/Desc/K12/Honest/ReadWhole.lean) at a state t before the switch's sending; the symbols that
are returned are under "there is". A code switch is a step of a proximity test. `SwitchFront` is
general in the dealt groups of columns. Its field `read` depends on the trees in which the old rows
are: it says that the reading of the old rows (`Tw.L9.readOld`, Johnson/Top/H0/Tw/L9/Switch.lean)
accepts after the switch's own sending, at the input `swIn` (FormSwitch.lean), and leaves no column.
One definition and one theorem, general in all their parameters: the old rows' oracle messages may
be in any number of trees. The file does not depend on the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean).

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of a place at which a
proximity test is. t (`T12`, Johnson/Desc/K12/Join.lean) is the state that is carried inside a
proximity test; `t.st` is its statement and `t.book` its book (`TreeBook`, OnBytes/Iop/Ground.lean:
the trees sent so far, and for each oracle message its tree and its part of that tree). dS and dC
are the switch's two declared rounds, gs the groups of columns dealt to them, rows the old rows
(`SingleRows`, OnBytes/Iop/Fold.lean). D (`Taken`, Johnson/Desc/K12/Law/SwDid.lean) is what a switch
has taken of its two rounds and has made on its way. places, TT and cs are the parameters of
`ReadAsks`.

  `read_swIn`: under `ReadAsks` at `frontIn p dS dC t gs rows` and the positions `swPos rC D`
    there is a y such that `readOld` at `swIn` and these positions is
    `.ok (bump B (treesAt places), [], y)`, where B is the book of `swD2` (FormSwitch.lean), the
    book after the sending. So the reading accepts, leaves no column, and counts one list more at
    each old tree of that book (`bump`, Johnson/Desc/K12/Honest/ReadTrees.lean; `treesAt`,
    ReadWhole.lean). The symbols that it returns are under "there is": the field `read` names
    `D.y` for them
  `frontIn p dS dC t gs rows`: a definition: what the reading would be given (`Tw.L9.SwIn`) before
    the switch's sending: the state's statement and book, the place's first tree
    (`p.nums.firstTree`), the dealt columns with their keys (`keyed`, Join.lean), the single rows.
    The other seven fields (`T`, `grp`, `ids`, `entry`, `settled`, `drawn`, `itemsLeft`), which
    neither `ReadAsks` nor `readOld` reads, are fillers with fixed values

By what. `read_swIn` is `read_yes_trees` (ReadWhole.lean) at what `readAsks_behind`
(Johnson/Desc/K12/Honest/ReadBehind.lean) gives from the hypothesis. The equations that
`readAsks_behind` has as hypotheses, between the fields of `swIn` and those of `frontIn`, hold by
`rfl`.

Limits. `ReadAsks` at `frontIn` is a hypothesis: it is not shown in this file. t is a free
parameter: nothing says that it is a state of the verifier's in any run. Of y the theorem says only
that there is one; that it is `D.y` is not stated. The other fields of `SwitchFront` are not
treated. `read_swIn` is called by nothing: Johnson/Desc/K12/Honest/Shape/ReadFirst.lean, which uses
`frontIn`, calls `readAsks_behind` and `read_yes_trees` itself. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.ReadBehind
import Johnson.Prover.Link.FormSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open Johnson.Prover.Link (swIn swPos swD2 swTarget)

/-- What the reading of the old rows would be given before the switch's sending: the statement and
the book of `t`, the first tree of `p`, the dealt columns `gs` with their keys, and `rows`. The
other seven fields are fillers with fixed values. -/
def frontIn (p : P12) (dS dC : Fmt.DeclaredRound) (t : T12) (gs : List (List (Nat × List UInt64)))
    (rows : SingleRows) : Tw.L9.SwIn :=
  { st := t.st, book := t.book, firstTree := p.nums.firstTree, opened := keyed p [dS, dC] gs
    old := rows, T := default, grp := 0, ids := #[], entry := default, settled := true
    drawn := ⟨[], [], [], none⟩, itemsLeft := 0 }

/-- **The switch's reading accepts at a list of trees.** Under `ReadAsks` at `frontIn`, `readOld` at
`swIn` returns the book after the sending with one list more counted at each tree of
`treesAt places`, no column, and some symbols y. -/
theorem read_swIn (p : P12) (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound) (t : T12)
    (rC : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (rows : SingleRows) (gp : Nat) (D : Taken)
    (places : Array (Nat × Nat)) (TT : Nat → Tree) (cs : Nat → List Tw.L9.Col)
    (A : ReadAsks (frontIn p dS dC t gs rows) (swPos rC D) places TT cs) :
    ∃ y, Tw.L9.readOld (swIn p n last dS dC t rC gs rows gp D) (swPos rC D) =
      .ok (bump (swD2 p n last dS dC t gs D).book (treesAt places), [], y) :=
  read_yes_trees _ _ places TT cs
    (readAsks_behind (i' := swIn p n last dS dC t rC gs rows gp D) A D (swTarget p n)
      (othersOf last n) (sentOf (swTarget p n) (othersOf last n)) p.nums.firstTree t.roots rfl rfl
      rfl rfl rfl)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.read_swIn
#print axioms ProofFile.Honest.K12.frontIn
