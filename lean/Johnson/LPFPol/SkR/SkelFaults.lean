-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/SkR/SkelFaults.lean: A TWIN, MADE BY PROGRAM, of
Johnson/Desc/ProofFile/Law/Skel/SkelFaults.lean: that file's text with two fields more in the
skeleton: a block's rounds and its oracles, whole. The namespace is LPFPol.SkR. What follows is that
file's own head, less its labels and with `lotSk`'s two arguments in their order; two
docstrings that are a label alone there are written out here.
`faultsOf` (ProofFile/Frames1.lean) AND `faultsAt`
(ProofFile/OnlineDescriptionFromBlockTables.lean) READ SKELETONS ALONE: each is its own text on skeletons, words and all.
Definitions, statements and proofs.
  `filter_skel`
  `faultsOfSk`, `faultsOf_skel`
  `LotSk`, `lotSk G L`: a lot less its functions, at the segments' records G: its name, `letters`,
    `still`, its blocks' skeletons; at a place, the skeleton of the batching that it makes at the
    gatherer that gathers nothing, if it supplies one; at a segment's number, whether it supplies
    `each`, and whether `tests`
  `faultsSk`, `faultsAt_skel`
Limits. That either list is empty anywhere is not said. Nothing on soundness.

-/
import Johnson.LPFPol.SkR.Skel
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol.SkR
open ProofFile
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem filter_skel {S Cl : Type} (bs : List (Block S Cl)) (p : Skel → Bool) :
    (bs.map skel).filter p = (bs.filter fun b => p (skel b)).map skel := by
  rw [List.filter_map]
  rfl

/-- `faultsOf` on skeletons. -/
def faultsOfSk (shape : List (String × Place)) (own : List Skel) : List String :=
  let fr := (own.filter fun o => o.place.kind == KindName.frame).map fun o =>
    (roleOf shape o.place, o)
  ((own.filter fun o =>
      o.place.kind != KindName.frame && !(shape.any fun b => b.2 == o.place)).map fun o =>
    "the block " ++ o.name ++ " stands at no place of the chain") ++
  (fr.filterMap fun x =>
    let o := x.2
    if x.1 == .stray then some ("the block " ++ o.name ++ " stands where no frame can be supplied")
    else if x.1 != .common && !((o.nRounds == 0) && o.bare) then
      some ("the block " ++ o.name ++ " is of the kind frame and has a round " ++
        "or states claims, or acts after the batching")
    else if !o.planOk && (match x.1 with | .lay _ => true | .clear _ => true | _ => false) then
      some ("the block " ++ o.name ++
        " starts or ends a link, and its test on the plan says no: only " ++
        "its decision is passed on, so that test would be asked nowhere")
    else if 1 < (fr.filter fun y => y.1 == x.1).length && x.1 != .common then
      some ("the role of the block " ++ o.name ++ " is taken by more than one block")
    else none) ++
  (shape.filter fun b => 1 < (own.filter fun o => o.place == b.2).length).map fun b =>
    "the place " ++ b.1 ++ " is taken by more than one block"

/-- The list of `faultsOf` is `faultsOfSk` at the shape and the blocks' skeletons. -/
theorem faultsOf_skel (shape : List (String × Place)) (own : List (Block S ProofFile.Cl)) :
    faultsOf shape own = faultsOfSk shape (own.map skel) := by
  have hfr : ((own.map skel).filter fun o => o.place.kind == KindName.frame).map
        (fun o => (roleOf shape o.place, o)) =
      ((own.filter fun o => o.place.kind == KindName.frame).map fun o =>
        (roleOf shape o.place, o)).map fun x => (x.1, skel x.2) := by
    rw [filter_skel, List.map_map, List.map_map]
    rfl
  unfold faultsOf faultsOfSk
  dsimp only
  rw [hfr]
  congr 1
  · congr 1
    · rw [filter_skel, List.map_map]
      rfl
    · rw [List.filterMap_map, List.filterMap_map, List.filterMap_map]
      refine List.filterMap_congr fun x _ => ?_
      simp only [Function.comp_def, List.filter_map, List.length_map, ← bare_skel,
        ← noRounds_skel]
      rfl
  · refine congrArg (List.map _) (List.filter_congr fun b _ => ?_)
    rw [filter_skel, List.length_map]
    rfl

/-- A lot less its functions. -/
structure LotSk where
  name : String
  letters : Bool
  still : List String
  blocks : List Skel
  batch : Place → Option Skel
  each : Nat → Bool
  tests : Nat → Bool

/-- **The skeleton of a lot**, at the segments' records G. -/
def lotSk (G : Ground) (L : Lot) : LotSk :=
  { name := L.name, letters := L.letters, still := L.still, blocks := (L.blocks G).map skel
    batch := fun a => (L.batch G a).map fun mk => skel (mk fun s => .ok ([], s))
    each := fun l => (L.each G l).isSome, tests := fun l => (L.tests G l).isSome }

/-- `faultsAt` on skeletons. -/
def faultsSk (spots : List Spot) (shape : List (String × Place)) (batchAt : List (Nat × Place))
    (lots : List LotSk) : List String :=
  let blocks := lots.flatMap fun L => L.blocks
  let many := fun (f : LotSk → Bool) => decide (1 < (lots.filter f).length)
  let atPlaces := spots.flatMap fun p =>
    let gives := lots.filter fun L => (L.batch p.place).isSome
    (if gives.isEmpty then []
     else
      (if !(batchAt.any fun x => x.2 == p.place) then
        ["the batching is supplied as a function at " ++ p.name ++
          ", where the driver does not ask for it"]
       else []) ++
      (if gives.any fun L => ((L.batch p.place).map fun k => k.place != p.place).getD false
        then ["the batching that is supplied as a function at " ++ p.name ++
          " makes a block that bears another place"]
       else []) ++
      (if 1 < gives.length then
        ["two tables of blocks supply the batching as a function at " ++ p.name] else []) ++
      (if gives.any (·.letters) then
        ["a table that says it depends on the request supplies the batching as a function at " ++
          p.name]
       else []) ++
      (if blocks.any fun b => b.place == p.place then
        ["the place " ++ p.name ++ " has both a block and the batching as a function"] else []))
  let onRoad := batchAt.filterMap fun x =>
    if lots.any fun L => (L.batch x.2).isSome then some x.1 else none
  let batchNames := spots.filterMap fun p =>
    if batchAt.any fun x => x.2 == p.place then some p.name else none
  let joined := (blocks.filter fun b => b.place.kind == KindName.frame).filterMap fun b =>
    match roleOf shape b.place with
    | .behind _ n =>
      if batchNames.contains n then
        some ("the block " ++ b.name ++ " would be joined after the batching at " ++ n ++
          ": it would end up in no chain")
      else none
    | _ => none
  let atLinks := ((spots.filterMap fun p => p.place.link).eraseDups).flatMap fun l =>
    (if many fun L => L.each l then
      [s!"two tables of blocks supply Link.each for link {l}"]
     else []) ++
    (if !onRoad.contains l && lots.any fun L => L.each l then
      [s!"Link.each is supplied for link {l}, which has no batching as a function: it is idle"]
     else []) ++
    (if many fun L => L.tests l then
      [s!"two tables of blocks supply Link.tests for link {l}"]
     else [])
  let names := shape.map (·.1)
  let twice := (names.filter fun n => 1 < names.count n).eraseDups.map fun n =>
    "two places bear the name " ++ n
  faultsOfSk shape blocks ++ twice ++ atPlaces ++ joined ++ atLinks

/-- Premise hB: the base's blocks are the lots'. Then the list of `faultsAt` is `faultsSk` at the
base's places, shape and batchings' places and at the lots' skeletons. -/
theorem faultsAt_skel (T : PureSeat) (B : PureBase)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) :
    faultsAt T B = faultsSk B.spots B.shape B.batchAt (T.lots.map (lotSk B.G₀)) := by
  have hbl : (B.all.flatMap fun x => x.2).map skel =
      (T.lots.map (lotSk B.G₀)).flatMap fun L => L.blocks := by
    rw [hB, List.flatMap_map, List.flatMap_map, List.map_flatMap]
    rfl
  unfold faultsAt faultsSk
  dsimp only
  rw [← hbl, ← faultsOf_skel]
  simp only [filter_skel, List.any_map, List.filter_map, List.length_map, List.isEmpty_map,
    List.filterMap_map, Function.comp_def, lotSk, Option.isSome_map, Option.map_map]
  rfl

end LPFPol.SkR

#print axioms LPFPol.SkR.filter_skel
#print axioms LPFPol.SkR.faultsOf_skel
#print axioms LPFPol.SkR.faultsAt_skel
