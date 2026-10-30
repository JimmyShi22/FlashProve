-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Stage.lean: one chain of a file as an interactive oracle reduction that takes over
trees from the chains before it and leaves trees to the chains behind it. Definitions alone.

OnBytes/Maker/Whole.lean has the three chains of a file as one reduction. Here the file is cut at
its seams: each chain is a reduction of its own, so that the three can be laid behind each other by
the library's `IOR.seq` and a statement on the whole can be had chain by chain.

A stage's implicit instance is the stored table and the trees that earlier chains have left. Its
prover's oracles are the chain's own trees. What it leaves is the stored table again, the trees
taken over that pass through, and those of its own trees that a later chain opens. A tree is named
by its number over the whole file, as in Whole.lean; `base` is the number of the chain's first own
tree.

A stage has the chain's written rounds alone: no round in front. The front round, the joining round
and the seam are laid in front of the three stages by whoever joins them. OnBytes/Maker/Row.lean
lays the three stages in a row; RowWhole.lean compares
the row with `reductionOfWholeFile`, one way, under `RowFit`.

What the file contains.
  `StageD`: the data. `Lin`: the trees at hand, `Lout`: the trees left, each with its number over
    the whole file and its depth (`LeftT`, OnBytes/Maker/Preamble.lean).
  `posL`: the position at (tree, leaf) in a list of trees left.
  `sWants`, `sExtPos`, `sOwnPos`, `sCol`, `sCarries`, `sView`: Whole.lean's `wants₁`, `extPosOf`,
    `ownPosOf`, `colOf`, `carriesOf`, `viewOf` for one chain.
  `sLeft`: the column of a tree left, at a leaf: taken over, or the chain's own.
  `stageIOR`: the reduction of a chain that hands claims on.
  `lastIOR`: the reduction of a last chain: to the trivial statement.

What is not claimed. No law is stated here. That a tree of `Lout` is at hand or the chain's own,
with that depth: elsewhere the oracle left holds empty columns. The stored table is handed on by
every `stageIOR`, whether a later chain opens it or not. The field `tie` is the empty set and the
field `blinded` is constant; nothing is said here of what these two fields are read for.


-/
import OnBytes.Maker.Whole
import OnBytes.Maker.Preamble

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- The data of one chain of a file. -/
structure StageD where
  /-- the stored table's depth -/
  a : ℕ
  /-- the number over the whole file of the chain's first own tree -/
  base : ℕ
  /-- the trees of earlier chains that are at hand -/
  Lin : List LeftT
  ds : List RDT
  /-- under which key a tree's columns stand in the chain's view -/
  key : ℕ → ℕ
  /-- the trees that are left to later chains -/
  Lout : List LeftT

/-- The position at (the tree with the number j, leaf x) in a list of trees left. -/
def posL (L : List LeftT) (j x : ℕ) : Option (PosL L) :=
  (List.finRange L.length).findSome? fun i =>
    if (L.get i).no = j then (if h : x < 2 ^ (L.get i).a then some ⟨i, ⟨x, h⟩⟩ else none) else none

namespace StageD
variable (S : StageD)

/-- The depth of the tree with the number j over the whole file. -/
def depth (j : ℕ) : Option ℕ :=
  if j < S.base then (S.Lin.find? (·.no == j)).map (·.a)
  else (treeShT S.ds (j - S.base)).map (·.a)

/-- The implicit instance: the stored table and the trees at hand. -/
abbrev Ei : ExtSpec := (oneExternalString (2 ^ S.a) SgX).prod (EjOf S.Lin)

/-- What is left: the stored table and the trees left. -/
abbrev Eo : ExtSpec := (oneExternalString (2 ^ S.a) SgX).prod (EjOf S.Lout)

end StageD

section
variable (C : CK) (S : StageD)

/-- The chain's wants, from the verifier's messages. -/
def sWants (ρ : Rho (uLT C S.ds)) : List Want := wantsOf S.a S.depth S.ds (drawnT C S.ds ρ)

/-- A want as a position of the implicit instance. -/
def sExtPos : Want → Option S.Ei.Pos
  | .table _ x => if h : x < 2 ^ S.a then some (.inl ⟨x, h⟩) else none
  | .tree j x => if j < S.base then (posL S.Lin j x).map .inr else none

/-- A want as a position of the prover's oracles. -/
def sOwnPos : Want → Option (OPos (uLT C S.ds))
  | .table _ _ => none
  | .tree j x => if j < S.base then none else posAtST C S.ds (j - S.base) x

/-- The column at a want. -/
def sCol (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) : Want → Option (List UInt64)
  | .table _ x => if h : x < 2 ^ S.a then some (y.1 ⟨x, h⟩).2 else none
  | .tree j x =>
    if j < S.base then (posL S.Lin j x).map y.2 else colAtST C S.ds τ (j - S.base) x

/-- Every symbol read of the stored table carries the position at which it was read. -/
def sCarries (y : S.Ei.Str) (ws : List Want) : Bool :=
  ws.all fun w => match w with
    | .table _ x => if h : x < 2 ^ S.a then (y.1 ⟨x, h⟩).1 == x else false
    | .tree _ _ => true

/-- The chain's view. -/
def sView (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) : View where
  rounds := rvT C S.ds τ
  opened := (sWants C S (rhoT C S.ds τ)).filterMap fun w => (sCol C S y τ w).map fun c =>
    match w with
    | .table item x => (Fmt.storedKey item, x, c)
    | .tree j x => (S.key j, x, c)

/-- The tests that stand before the run: the work, the parts of the draws, the table's symbols. -/
def sTests (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) : Bool :=
  passT C S.ds (rhoT C S.ds τ) && fullOf S.ds (drawnT C S.ds (rhoT C S.ds τ)) &&
    sCarries S y (sWants C S (rhoT C S.ds τ))

/-- The column of a tree left, at a leaf. -/
def sLeft (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (p : PosL S.Lout) : List UInt64 :=
  (sCol C S y τ (.tree (S.Lout.get p.1).no p.2.val)).getD []

/-- **The reduction of a chain that hands claims on.** run: from the explicit instance and the view
to the claims. -/
@[reducible] def stageIOR {Xi Xo : Type} (run : Xi → View → Option Xo) : IOR Xi S.Ei Xo S.Eo where
  shape := uLT C S.ds
  blinded := fun _ => true
  extReads := fun ρ => ((sWants C S ρ).filterMap (sExtPos S)).toFinset
  reads := fun ρ => ((sWants C S ρ).filterMap (sOwnPos C S)).toFinset
  out := fun x y τ => if sTests C S y τ then run x (sView C S y τ) else none
  imp := fun y τ => (y.1, sLeft C S y τ)
  srcE := fun _ q => match q with
    | .inl p => {.inl p}
    | .inr p => (sExtPos S (.tree (S.Lout.get p.1).no p.2.val)).toFinset
  srcO := fun _ q => match q with
    | .inl _ => ∅
    | .inr p => (sOwnPos C S (.tree (S.Lout.get p.1).no p.2.val)).toFinset
  tie := fun _ _ => ∅

/-- **The reduction of a last chain.** run: from the explicit instance and the view to the
verdict. -/
@[reducible] def lastIOR {Xi : Type} (run : Xi → View → Bool) : IOR Xi S.Ei Unit extNone where
  shape := uLT C S.ds
  blinded := fun _ => true
  extReads := fun ρ => ((sWants C S ρ).filterMap (sExtPos S)).toFinset
  reads := fun ρ => ((sWants C S ρ).filterMap (sOwnPos C S)).toFinset
  out := fun x y τ => if sTests C S y τ && run x (sView C S y τ) then some () else none
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

end

end OnBytes.Maker
