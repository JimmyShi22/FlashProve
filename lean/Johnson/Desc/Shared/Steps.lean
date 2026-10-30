-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Steps.lean: rounds 3 to 7 of the shared chain: the positions, the sending of
Omega, the second point and the split.

Definitions only; no theorem is stated. The words are explained in State.lean, and what has been run
and what is not checked is told in Fold.lean.

Main names:
  readStoredP: follows Blk.readStored (OnBytes/Iop/Ground.lean). The stored table's columns must be
    the next opened columns: under the tree key of the stored table (Fmt.storedKey), at the
    positions of the list, of the table's width, in order. Whether a column lies under the table's
    root is not checked: a view holds no root.
  step2 (round 3, "LOC"): follows the last lines of foldeqVerify, and foldeqColumnsVerify
    (OnBytes/Iop/Foldeq.lean). The positions are drawn, and each draw adds one row to G_u's group.
  step3 (rounds 4 and 5): follows linSharedVerify (OnBytes/Iop/Lin.lean). Omega is sent, with the
    split's mask message where a split is needed. Omega must be alone in its tree. The messages join
    their groups.
  step4 (round 6, "LIN zeta"): the point on the rows of the matrix is drawn.
  halfOf, step5 (round 7, "SPLIT"): follows linSharedVerify and splitVerify
    (OnBytes/Iop/Split.lean). The row that the program calls (Fold) is built from the named values.
    It is split over the two groups with the next free mask entry and the share that the round
    holds. Where G_u and Omega have the same code there is no such round, and the row goes to the
    one group.

readStoredP, the checks on the rounds, halfOf and the conditions of the split are written a second
time here: they are not calls of the program's routines.

What is not claimed. That a check which is written a second time here is the same as the program's.
Nothing on soundness, on an honest prover or on hiding.
What this comment says of the code rests on reading and is not machine-checked.


-/
import Johnson.Desc.Shared.Step0
import Johnson.Desc.Shared.Step1
import OnBytes.Iop.Split

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.Shared
open OnBytes OnBytes.Params

/-- Reads the stored table's columns at the table's part of the draws: they must be the next opened
columns. Returns the list of positions (each once, increasing), the columns at the list, and the
state without them. Whether a column lies under the table's root is not checked here. -/
def readStoredP {L : Type} (d : DState L) (t : Fmt.Stored) (pos : Positions) :
    Option (Array Nat × Array (Array F) × DState L) :=
  let xs := listOfT ((Fmt.partOf t pos.draws.toList).map (· % 2 ^ t.sh.a))
  let got := d.opened.take xs.length
  if got.length == xs.length && Blk.columnsFit (Fmt.storedKey t.item) t.sh.W got xs then
    some (xs.toArray, (got.map fun y => y.2.2.toArray).toArray,
      { d with opened := d.opened.drop xs.length })
  else none

/-- Round 3, "LOC": the positions. -/
def step2 (G : Ground Loc) (p : Par) (d : DState Loc) : List Fmt.RoundView → Option (DState Loc)
  | [r] => do
    let S := p.S.fold
    let s := S.index
    let pos := Positions.ofDraws s.code.logN r.drawn.poss
    if r.vals.isEmpty && r.drawn.elems.isEmpty && r.drawn.trits.isEmpty &&
        decide (0 < r.drawn.poss.length) && pos.draws.size == S.columns then
      let l : Loc := { d.loc with pos := pos }
      let (list, columns, d₁) ← readStoredP d ⟨s.tree, s.saltBytes, p.key.item, 0, S.columns⟩ pos
      let rows ← (l.pos.draws.toList.take S.columns).mapM fun x => do
        let i ← list.idxOf? x
        foldeqColumnRow S x (foldeqSymbol (eqGammaOf p l) (← columns[i]?)) l.u
      let d₂ ← G.addRows p d₁ l.gU rows
      some { d₂ with loc := l }
    else none
  | _ => none

/-- Rounds 4 and 5: the sending of Omega. -/
def step3 (G : Ground Loc) (p : Par) (d : DState Loc) : List Fmt.RoundView → Option (DState Loc)
  | [r₁, r₂] => do
    let (ids, sd, an, d₁) ← sendP G p d (linMessageOmega p.S) r₁ r₂
    let omega ← ids[0]?
    let split ← if p.S.sharedSplitNeeded then ids[1]? else some noId
    let l : Loc := { d.loc with idsO := ids, sdO := sd, anO := an, omega := omega, split := split }
    if linAloneInItsTree d₁.book omega then
      let d₂ ← G.join p d₁ l.gO omega false
      let d₃ ← if p.S.sharedSplitNeeded then
          (G.join p d₂ l.gO split false).bind fun e => G.join p e l.gU split false
        else some d₂
      some { d₃ with loc := l }
    else none
  | _ => none

/-- Round 6: the point on the rows of the matrix. -/
def step4 (p : Par) (d : DState Loc) : List Fmt.RoundView → Option (DState Loc)
  | [r] =>
    if drawnOnly r p.S.kRow then
      some { d with loc := { d.loc with zeta := r.drawn.elems.map E.ofTriple } }
    else none
  | _ => none

/-- The part of a row that reads members of a group (first = true), or the part that reads the other
oracle messages (first = false). The target and the kind are left at the record's defaults. -/
def halfOf (row : Row) (members : Array Nat) (first : Bool) : Row :=
  { terms := row.terms.filter fun t => members.contains t.oracle == first
    units := row.units.filter fun u => members.contains u.oracle == first
    runs := row.runs.filter fun w => members.contains w.oracle == first
    forms := row.forms.filter fun f => members.contains f.oracle == first }

/-- Round 7, "SPLIT": the row (Fold) and its split. -/
def step5 (G : Ground Loc) (p : Par) (d : DState Loc) (rs : List Fmt.RoundView) : Option (DState Loc) := do
  let l₀ := d.loc
  let row ← linFoldRow p.S l₀.psi l₀.zeta l₀.u l₀.omega (linLayOmega d.st.codes p.S)
  if p.S.sharedSplitNeeded then
    match rs with
    | [r] =>
      let G1 ← d.st.groups[l₀.gO]?
      let G2 ← d.st.groups[l₀.gU]?
      let m ← d.st.oracles[l₀.split]?
      let share ← match r.vals with
        | [.e x] => some (E.ofTriple x)
        | _ => none
      let l : Loc := { l₀ with share := share }
      if l.gO != l.gU && row.kind == .plain && m.shape.mainRows == 0 &&
          G1.members.contains l.split && G2.members.contains l.split &&
          row.oracles.all (fun o => G1.members.contains o != G2.members.contains o) &&
          silent r then
        let (kappa, d₁) ← G.takeMask p d l.split
        let d₂ ← G.addRow p d₁ l.gO
          { (halfOf row G1.members true).addUnit l.split .mask kappa oneE with target := l.share }
        let d₃ ← G.addRow p d₂ l.gU
          { (halfOf row G1.members false).addUnit l.split .mask kappa (negE oneE) with
            target := subE row.target l.share }
        some { d₃ with loc := l }
      else none
    | _ => none
  else
    match rs with
    | [] => G.addRow p d l₀.gU row
    | _ => none

end Desc.Shared
