-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/L3/Frame.lean: THE FRAME OF THE SMALLNESS TEST's MESSAGES, AS PLAIN FUNCTIONS ON
DATA. Five written rounds a link: the sending of the reads (2) · the draw of the matrix (1) · the
sending of the digits (2). The lookup on the digits, which follows, and a sending itself are not
written here: they are parameters.
TYPED AFTER THE PROGRAM's TEXT (the verifier on bytes under OnBytes/; the line numbers in the list
are not held against these files).
THE LIST: guard · the program's file:line · the step's name here.
  (c1) the link is neither handed nor done
       OnBytes/Model/Trees.lean:226 · commitFront
  (c2) the link's number is the walk's
       OnBytes/Model/Trees.lean:214 · commitFront
  (c3) [the sending: ChainCheck.later]
       OnBytes/Model/Trees.lean:228 · the parameter send
  (c4) each array named: not committed yet; born at this link; laid by the layout at this moment
       OnBytes/Model/Trees.lean:232-241 · commitBehind
  (c5) as many arrays named as the layout lays here
       OnBytes/Model/Trees.lean:242 · commitBehind
  (t1) the list of tables is closed
       OnBytes/Model/Tail.lean:718 · drawFront
  (t2) one shape a matrix
       OnBytes/Model/Tail.lean:719 · drawFront
  (o1) THE ORDER: all that the matrix is applied to is sent, sampled and answered
       OnBytes/Model/Tail.lean:697-703 · orderGuard
       (arrayFixed: the program's own plain function, :675-688)
  (d1) NM + 1 first columns; a column is there
       OnBytes/Model/Tail.lean:664 · drawStep
  (d2) combinations are not 0
       OnBytes/Model/Rounds.lean:160 · drawStep
  (d3) the format's kind of the name "RNG"
       OnBytes/Model/Rounds.lean:93 · drawStep
  (d4) the plan's next entry: its name, no draw that is never 0, the last round's debt is paid
       OnBytes/Iop/Ground.lean:822-825 · drawStep (the entry and "settled" are arguments)
  (d5) a round is there
       OnBytes/Iop/Ground.lean:838-839 · drawStep
  (d6) no item is left in the round; as many elements, positions, matrix entries as the entry says
       OnBytes/Iop/Ground.lean:841-842 · drawStep
  (d7) the entry draws no element, no position, columns * combinations matrix entries
       OnBytes/Model/Rounds.lean:96 · drawStep
  (d8) the entry counts no batched rows
       OnBytes/Iop/Ground.lean:602-605, :825 · drawStep
       (in the program an entry that counted rows would leave a debt; a count asked in between would
       pay it (Blk.requireRows), but between this draw and the next round's close transcriptF asks
       none (OnBytes/Model/Tail.lean:722-723): so the NEXT close would refuse: here the step asks
       it of its own entry)
(d3) cannot fail: a constant of the library. THE ORDER OF THE REFUSALS IS THE PROGRAM's: the entry
(d4) in front of the round (d5).
WHOSE IS THE CHANNEL's STATE. Blk.close also WRITES: entries := the rest · last := this entry ·
askedRows := false · cur | left. These steps take the entry and "settled" as arguments and hand
nothing of that on: which entry and which rounds a step gets is the matter of the fold and of the
table of stretches, which are not written here; "last := this entry" is what the next round's
"settled" hangs on: with (d8) that debt is none.
No theorem. No soundness is claimed.

-/
import OnBytes.Model.Tail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace L3
open OnBytes OnBytes.Model

/-- (c1) (c2). -/
def commitFront (L : LinkCtx) : Except String Unit :=
  if !(!L.handed && !L.done) then .error "plan-link: handed or done"
  else if !(L.link == L.check.link) then .error "chain-refused: the link's number"
  else .ok ()

/-- The arrays that the layout lays at the link's present moment. -/
def laidHere (L : LinkCtx) : List (String × Nat) :=
  (L.check.arraysOf L.link).filter fun a => L.check.momentOfMessage L.link a.2 == some L.moments

/-- (c4), for one array: the mark. -/
def commitOne (L : LinkCtx) (F : Fork) (t : Nat) : Except String Fork :=
  let committed := ((F.trees[t]?).map (·.root.isSome)).getD true
  let here : Bool :=
    match L.arrayOf[t]? with
    | some (born, name) => born == L.link && (laidHere L).any fun a => a.1 == name
    | none => false
  if !committed && here then .ok (F.rootTaken t 0) else .error s!"plan-link: array {t}"

/-- (c4) (c5). L: the link's record IN FRONT of the sending; check: what the sending hands back. -/
def commitBehind (L : LinkCtx) (check : ChainCheck) (F : Fork) (trees : List Nat) :
    Except String (LinkCtx × Fork) := do
  let F ← trees.foldlM (commitOne L) F
  if trees.length == (laidHere L).length then
    pure ({ L with check := check, moments := L.moments + 1 }, F)
  else throw "plan-link: the number of arrays"

/-- (o1) THE GUARD OF ORDER. S: the chain's statement. -/
def orderGuard (tl : HTailF2) (L : LinkCtx) (S : Statement) : Bool :=
  L.check.link == L.link && decide (L.link < L.check.links) && tl.gtTree.size == tl.NM &&
    tl.gtTree.all (HTailF2.arrayFixed L S) &&
    (List.range 4).all fun n => (tl.ix.U.getD n none).all (HTailF2.arrayFixed L S)

/-- (t1) (t2) (o1). -/
def drawFront (tl : HTailF2) (L : LinkCtx) (S : Statement) : Except String Unit :=
  if !tl.funClosed then .error "internal-f-fun-open"
  else if !(tl.shp.size == tl.NM) then .error "internal-t2f-map"
  else if !orderGuard tl L S then .error "internal-f-matrix-order"
  else .ok ()

/-- (d1) … (d8) THE DRAW. e: the plan's next entry; settled: the last round owes no question; rs:
the step's one round. -/
def drawStep (tl : HTailF2) (e : Option Fmt.Entry) (settled : Bool) (rs : List Fmt.RoundView) :
    Except String HTailF2 :=
  let cfFirst := tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0]
  if !(cfFirst.size == tl.NM + 1 && tl.foldColumns != 0) then .error "refused: the list of matrices"
  else if tl.tau == 0 then .error "refused: no combination"
  else if !(Params.kindOf rngName == some .entries) then .error "refused: the name's kind"
  else match e with
    | none => .error "plan: no entry"
    | some e =>
      if e.name != rngName || e.drawNZ != 0 || !settled then .error "plan: the entry"
      else match rs with
        | [] => .error "view-shape: no round"
        | [r] =>
          if !(r.vals.isEmpty && r.drawn.elems.length == e.drawE && r.drawn.poss.length == e.poss &&
              r.drawn.trits.length == e.trits) then .error "view-shape: the round"
          else if !(e.drawE == 0 && e.trits == tl.foldColumns * tl.tau && e.poss == 0) then
            .error "refused: the entry's counts"
          else if !(e.rows == 0) then .error "plan: the entry counts rows"
          else .ok { tl with cfF := r.drawn.trits.toArray, cfFirst := cfFirst }
        | _ => .error "view-shape: more than one round"

/-! ## The stretch as steps on one state -/

/-- What the frame's steps carry. W: what a sending's step carries beside the walk's record (the
statement, the book, the roots' count): a parameter; stOf reads the statement out of it. -/
structure St (W : Type) where
  L : LinkCtx
  F : Fork
  tl : HTailF2
  w : W

/-- A sending's step, as a parameter: the walk's record, its own state, its two rounds. -/
abbrev Send (W : Type) : Type := ChainCheck → W → List Fmt.RoundView → Except String (ChainCheck × W)

variable {W : Type}

/-- A COMMITMENT: two rounds. -/
def commitStep (send : Send W) (trees : List Nat) (s : St W) (rs : List Fmt.RoundView) :
    Except String (St W) := do
  commitFront s.L
  let (check, w) ← send s.L.check s.w rs
  let (L, F) ← commitBehind s.L check s.F trees
  pure { s with L := L, F := F, w := w }

/-- THE LIST OF TABLES IS CLOSED: no round. The program's own plain function. -/
def closeStep (funs : Array HFun) (s : St W) : Except String (St W) :=
  match s.tl.closeFuns funs with
  | some tl => .ok { s with tl := tl }
  | none => .error "refused: the list of tables was closed already"

/-- THE MATRIX: one round. The first free slot is noted, as the program notes it. -/
def matrixStep (stOf : W → Statement) (e : Option Fmt.Entry) (settled : Bool) (s : St W)
    (rs : List Fmt.RoundView) : Except String (St W) := do
  drawFront s.tl s.L (stOf s.w)
  let tl ← drawStep s.tl e settled rs
  pure { s with tl := { tl with slotA := s.F.next } }

/-- In the form that the fold takes: how many columns were taken: none. -/
def asStep {S : Type} (f : S → List Fmt.RoundView → Except String S) :
    S → List Fmt.RoundView → List (Nat × Nat × List UInt64) → Option (S × Nat) :=
  fun s rs _ => (f s rs).toOption.map fun x => (x, 0)

end L3
