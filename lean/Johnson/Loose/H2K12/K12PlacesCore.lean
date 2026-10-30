-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.K12MemberOfParts
/-
Johnson/Loose/H2K12/K12PlacesCore.lean: FOR THE PROXIMITY TEST's (the kind K12's)
ROW: placesAt (H2K12/K12MemberOfParts.lean: H2U.placesOfMade's text at its five reads) WITH WHAT IT
ASKS OF THE FIRST CHAIN's LONG LIST AS LETTERS: the three lists of trees, the count of "LOC", the
last test's cut. General; nothing is evaluated here.
WHY. At the written values Lean's kernel does not get through placesAt: treesSent goes through
routines of Lean's library that the kernel does not unfold, and through a check that costs the
square of the plan's length (by a reading of its text; not measured); the count and the cut carry
numbers along 48,293 rounds. Each of these
is had apart (H2K12/K12TreesOf.lean, H2K12/K12CutSplit.lean). What is left, placesCore, reads short
lists alone.
  firstsCore       firstsAt's text behind its three calls of treesSent; the count a letter.
                   laterCore: the like of H2U.placesLater's text
                   (Johnson/Desc/K12/Plan/PlaceOfPlan.lean). COPIES, sign for sign but for the
                   letters
  firstsAt_bind    firstsAt is its three calls of treesSent, then firstsCore: by unfolding: so a
                   copy that parts from its original makes this file red. placesLater_bind: the like
  placesCore       placesAt's text over firstsCore and laterCore, the cut a letter
  placesAt_core    FROM FIVE PREMISES, BY NAME: h0 h1 h2: treesSent returns t0 t1 t2 at the three
                   chains; hl: the count of "LOC" is locs; hT: cutLAt returns tL: placesAt … =
                   placesCore … locs tL t0 t1 t2
WHAT IT IS NOT: no value is named. No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes OnBytes.Params Johnson.G.OfPlan H2U
open Johnson.G (ChainSends)

/-- `firstsAt`'s text behind its three calls of `treesSent`. -/
def firstsCore (z : ProofSized) (locs : Nat) (t0 t1 t2 : List (Sent × Nat)) :
    Except String Firsts := do
  let S := z.batch.shape
  let riders := z.request.atStart.map (·.leafClass)
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some a => pure a
    | none => throw ("firstsOfPlan: the rule has no list for " ++ what)
  let l ← get "the last test" (frameOpens riders t0 locs)[locs]?
  let sh := sharedOpens S t1
  let u ← get "the folded row's test" (sh[1]?)
  let o :=
    if S.sharedSplitNeeded then
      (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x => (x.1.dropLast, 0)
    else none
  let w ← get "the own test"
    (secondOpens S (fun t => t.tag == .link 0 0 && riders.contains t.cls) t0 t1 t2).head?
  pure { L := (l, 0), U := (u.1, 0), O := o, W := (w, t0.length + 1) }

theorem firstsAt_bind (z : ProofSized) (P0 P1 P2 : Fmt.Plan)
    (c : ChainSends × ChainSends × ChainSends) :
    firstsAt z P0 P1 P2 c =
      (treesSent "proof file, first chain" c.1 P0 []).bind fun t0 =>
        (treesSent "proof file, shared chain" c.2.1 P1
          (ownMasks c.2.1.codes z.batch.shape P1.rounds)).bind fun t1 =>
          (treesSent "proof file, second chain" c.2.2 P2 []).bind fun t2 =>
            firstsCore z (P0.rounds.filter fun e => e.name == "LOC").length t0 t1 t2 := rfl

/-- `H2U.placesLater`'s text behind its three calls of `treesSent`. -/
def laterCore (A : LaterArgs) (t0 t1 t2 : List (Sent × Nat)) : Except String Later3 := do
  let S := A.batch.shape
  let a := A.set.samples
  let once := A.batch.lines.oneTime
  let w := fun (c : Scope) => A.set.workOf .query c
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("placesLater: " ++ A.file ++ ": nothing at " ++ what)
  let sh := sharedOpens S t1
  let fU ← get "the folded row's test's first trees" (sh[1]?)
  let fO : Option FirstAt :=
    if S.sharedSplitNeeded then
      (sh[2 + (switchOpens 0 .folded t1).length]?).map fun x => (x.1.dropLast, 0)
    else none
  let fW ← get "the own test's first trees" (secondOpens S A.input t0 t1 t2).head?
  let tU ← get "the folded row's test" ((batPlaces A.es1)[0]?.bind fun i => cutOn A.es1 1 i S.testU)
  let tO := (batPlaces A.es1)[1]?.bind fun i => cutOn A.es1 1 i S.testOmega
  let tW ← get "the own test" ((batPlaces A.es2)[0]?.bind fun i => cutOn A.es2 2 i S.testOwn)
  let rB := S.choice.masksRide
  pure
    { U := mkPlace a 2 A.batch.folded.stages (S.fold.index.answers + S.fold.columns + 1 + 2 * a)
        (w (if once then .once else .shared)) (!S.masksAhead) tU (fU.1, 0) 2 rB
      O := match tO, fO with
        | some tO, some fO =>
          some (mkPlace a 2 A.batch.omega.stages (1 + 2 * a) (w (if once then .once else .shared))
            true tO fO (2 + (tU.stages.length - 1)) rB)
        | _, _ => none
      W := mkPlace a 3 A.batch.own.stages (2 + 3 * a) (w (if once then .once else .request))
        (!S.masksAhead) tW (fW, t0.length + 1) (A.groupsFirst + 1) rB }

theorem placesLater_bind (A : LaterArgs) :
    placesLater A =
      (treesSent (A.file ++ ", first chain") A.c0 A.P0 []).bind fun t0 =>
        (treesSent (A.file ++ ", shared chain") A.c1 A.P1
          (ownMasks A.c1.codes A.batch.shape A.P1.rounds)).bind fun t1 =>
          (treesSent (A.file ++ ", second chain") A.c2 A.P2 []).bind fun t2 =>
            laterCore A t0 t1 t2 := rfl

/-- **`placesAt`'s text with the trees, the count and the cut as letters.** -/
def placesCore (set : Setting) (z : ProofSized) (Pl : List Planned) (P0 P1 P2 : Fmt.Plan)
    (c : ChainSends × ChainSends × ChainSends) (locs : Nat) (tL : TestCut)
    (t0 t1 t2 : List (Sent × Nat)) : Except String Places4 := do
  let Fs ← firstsCore z locs t0 t1 t2
  let get {α : Type} (what : String) (x : Option α) : Except String α := match x with
    | some v => pure v
    | none => throw ("placesOfMade: no cut at " ++ what)
  let gL := locs + 1
  let X ← laterCore (laterAt set z Pl P0 P1 P2 c (gL + (tL.stages.length - 1))) t0 t1 t2
  pure
    { L := mkPlace set.samples 1 z.last.stages
        (← get "the rows of the last test" (rowsAtLast z)) (set.workOf .query .request)
        false tL Fs.L gL z.request.choice.masksRide
      U := X.U, O := X.O, W := X.W }

/-- **placesAt, where the three lists of trees, the count and the cut are had.** -/
theorem placesAt_core {set : Setting} {z : ProofSized} {Pl : List Planned} {P0 P1 P2 : Fmt.Plan}
    {c : ChainSends × ChainSends × ChainSends} {locs : Nat} {tL : TestCut}
    {t0 t1 t2 : List (Sent × Nat)}
    (h0 : treesSent "proof file, first chain" c.1 P0 [] = .ok t0)
    (h1 : treesSent "proof file, shared chain" c.2.1 P1
      (ownMasks c.2.1.codes z.batch.shape P1.rounds) = .ok t1)
    (h2 : treesSent "proof file, second chain" c.2.2 P2 [] = .ok t2)
    (hl : (P0.rounds.filter fun e => e.name == "LOC").length = locs)
    (hT : cutLAt Pl z.request.last = some tL) :
    placesAt set z Pl P0 P1 P2 c = placesCore set z Pl P0 P1 P2 c locs tL t0 t1 t2 := by
  have hF : firstsAt z P0 P1 P2 c = firstsCore z locs t0 t1 t2 := by
    rw [firstsAt_bind, h0, h1, h2, hl]
    rfl
  have hX : ∀ g, placesLater (laterAt set z Pl P0 P1 P2 c g) =
      laterCore (laterAt set z Pl P0 P1 P2 c g) t0 t1 t2 := by
    intro g
    have e0 : treesSent ((laterAt set z Pl P0 P1 P2 c g).file ++ ", first chain")
        (laterAt set z Pl P0 P1 P2 c g).c0 (laterAt set z Pl P0 P1 P2 c g).P0 [] = .ok t0 := h0
    have e1 : treesSent ((laterAt set z Pl P0 P1 P2 c g).file ++ ", shared chain")
        (laterAt set z Pl P0 P1 P2 c g).c1 (laterAt set z Pl P0 P1 P2 c g).P1
        (ownMasks (laterAt set z Pl P0 P1 P2 c g).c1.codes
          (laterAt set z Pl P0 P1 P2 c g).batch.shape
          (laterAt set z Pl P0 P1 P2 c g).P1.rounds) = .ok t1 := h1
    have e2 : treesSent ((laterAt set z Pl P0 P1 P2 c g).file ++ ", second chain")
        (laterAt set z Pl P0 P1 P2 c g).c2 (laterAt set z Pl P0 P1 P2 c g).P2 [] = .ok t2 := h2
    rw [placesLater_bind, e0, e1, e2]
    rfl
  unfold placesAt placesCore
  rw [hF, hl, hT]
  simp only [hX]
  rfl

end H2K12

#print axioms H2K12.firstsAt_bind
#print axioms H2K12.placesLater_bind
#print axioms H2K12.placesAt_core
