-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelParts.lean: `partsAt`, `lackingAt` AND `PureParts.base`
(ProofFile/OnlineDescriptionFromBlockTables.lean) READ SKELETONS ALONE. Definitions, statements and proofs.
  `isSome_findSome`, `map_findSome`, `mapM_ok`: three small laws on lists
  `Steady G L`: the skeleton of a batching that the lot L makes is the same at every gatherer
  `makerSk`, `roadSk`, `onRoadSk`, `eachAtSk`, `testsAtSk`, `placesSk`, `framesSk`: `partsAt`'s
    parts on skeletons
  `maker_skel`, `road_skel` (under `Steady`), `road_triv`, `onRoad_skel`, `eachAt_skel`,
    `testsAt_skel`, `place_case`, `places_skel`, `frames_skel`   T16
  `lackingSk`, `lackingAt_skel`   T17, general in the parts
  `base_skel`: `PureParts.base` returns just where the places' skeletons all stand, and with these
Limits. No return is shown. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelFaults
import Johnson.Desc.ProofFile.Law.Skel.SkelChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-! ### three small laws on lists -/

universe u v w

theorem isSome_findSome {α : Type u} {β : Type v} (f : α → Option β) :
    ∀ l : List α, (l.findSome? f).isSome = l.any fun a => (f a).isSome
  | [] => rfl
  | a :: l => by
    rw [List.findSome?_cons, List.any_cons, ← isSome_findSome f l]
    cases f a <;> rfl

theorem map_findSome {α : Type u} {β : Type v} {γ : Type w} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, (l.findSome? f).map g = l.findSome? fun a => (f a).map g
  | [] => rfl
  | a :: l => by
    rw [List.findSome?_cons, List.findSome?_cons, ← map_findSome f g l]
    cases f a <;> rfl

theorem mapM_ok {α β γ : Type} (f : α → Except String β) (g : β → γ) :
    ∀ l : List α, (l.mapM f).map (List.map g) = l.mapM fun a => (f a).map g
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, ← mapM_ok f g l]
    cases f a <;> cases l.mapM f <;> rfl

theorem skel_guardMark (b : Block S ProofFile.Cl) : skel (guardMark b) = skel b := rfl

/-! ### partsAt on skeletons -/

/-- The skeleton of a batching that the lot makes is the same at every gatherer. -/
def Steady (G : Ground) (L : Lot) : Prop :=
  ∀ a mk, L.batch G a = some mk → ∀ g g', skel (mk g) = skel (mk g')

def makerSk (ks : List LotSk) (a : Place) : Option Skel :=
  (ks.filter fun L => !L.letters).findSome? fun L => L.batch a

def nameAtSk (spots : List Spot) (a : Place) (n : String) : String :=
  ((spots.find? fun p => p.place == a).map fun p => p.name).getD n

def roadSk (spots : List Spot) (ks : List LotSk) (a : Place) : Option Skel :=
  (makerSk ks a).map fun k => { k with name := nameAtSk spots a k.name }

def onRoadSk (batchAt : List (Nat × Place)) (ks : List LotSk) : List Nat :=
  batchAt.filterMap fun x => if (makerSk ks x.2).isSome then some x.1 else none

def eachAtSk (spots : List Spot) (ks : List LotSk) : List Nat :=
  ((spots.filterMap fun p => p.place.link).eraseDups).filter fun l =>
    (ks.filter fun L => !L.letters).any fun L => L.each l

def testsAtSk (spots : List Spot) (ks : List LotSk) : List Nat :=
  ((spots.filterMap fun p => p.place.link).eraseDups).filter fun l =>
    (ks.filter fun L => !L.letters).any fun L => L.tests l

def placesSk (spots : List Spot) (ks : List LotSk) : List (Spot × Except String Skel) :=
  spots.map fun p =>
    let looks := p.cuts.flatMap fun c => [stepName c.look, c.look]
    let here := ks.filterMap fun L =>
      (L.blocks.find? fun b => b.place == p.place).map fun b => (L, b)
    let sits := here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains)
    (p, match roadSk spots ks p.place, sits with
      | some f, _ => .ok f
      | none, some x => .ok { x.2 with name := p.name }
      | none, none =>
        match here with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here"))

def framesSk (shape : List (String × Place)) (ks : List LotSk) : List (FrameRole × Skel) :=
  ks.flatMap fun L =>
    if L.letters then []
    else (L.blocks.filter fun b => b.place.kind == KindName.frame).filterMap fun b =>
      match roleOf shape b.place with
      | .common => none
      | .stray => none
      | r => some (r, b)

section
variable (T : PureSeat) (B : PureBase)

theorem quiet_skel :
    ((T.lots.map (lotSk B.G₀)).filter fun L => !L.letters) =
      (T.lots.filter fun L => !L.letters).map (lotSk B.G₀) := by
  rw [List.filter_map]
  rfl

theorem maker_skel (a : Place) :
    (((T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a).map fun mk =>
      skel (mk fun s => .ok ([], s))) = makerSk (T.lots.map (lotSk B.G₀)) a := by
  unfold makerSk
  rw [quiet_skel, List.findSome?_map, map_findSome]
  rfl

theorem road_skel (hS : ∀ L ∈ T.lots, Steady B.G₀ L) (a : Place)
    (g : S → Except String (List ProofFile.Cl × S)) :
    ((partsAt T B).road.batch a).map (fun mk => skel (mk g)) =
      roadSk B.spots (T.lots.map (lotSk B.G₀)) a := by
  unfold roadSk
  rw [← maker_skel]
  show (((T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a).map _).map _ = _
  cases e : (T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a with
  | none => rfl
  | some mk =>
    obtain ⟨L, hL, hmk⟩ := List.exists_of_findSome?_eq_some e
    have hs := hS L (List.mem_of_mem_filter hL) a mk hmk g fun s => .ok ([], s)
    show some (skel { guardMark (mk g) with name := _ }) = some _
    refine congrArg some ?_
    show ({ skel (mk g) with name := nameAtSk B.spots a (skel (mk g)).name } : Skel) = _
    rw [hs]

/-- At the gatherer that gathers nothing: no premise. -/
theorem road_triv (a : Place) :
    ((partsAt T B).road.batch a).map (fun mk => skel (mk fun s => .ok ([], s))) =
      roadSk B.spots (T.lots.map (lotSk B.G₀)) a := by
  unfold roadSk
  rw [← maker_skel]
  show (((T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a).map _).map _ = _
  cases (T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a <;> rfl

theorem onRoad_skel :
    (partsAt T B).onRoad = onRoadSk B.batchAt (T.lots.map (lotSk B.G₀)) := by
  unfold onRoadSk
  simp only [← maker_skel, Option.isSome_map]
  rfl

theorem eachAt_skel : (partsAt T B).eachAt = eachAtSk B.spots (T.lots.map (lotSk B.G₀)) := by
  unfold eachAtSk
  simp only [quiet_skel, List.any_map, Function.comp_def]
  show List.filter (fun l => ((T.lots.filter fun L => !L.letters).findSome? fun L =>
    L.each B.G₀ l).isSome) _ = _
  simp only [isSome_findSome]
  rfl

theorem testsAt_skel : (partsAt T B).testsAt = testsAtSk B.spots (T.lots.map (lotSk B.G₀)) := by
  unfold testsAtSk
  simp only [quiet_skel, List.any_map, Function.comp_def]
  show List.filter (fun l => ((T.lots.filter fun L => !L.letters).findSome? fun L =>
    L.tests B.G₀ l).isSome) _ = _
  simp only [isSome_findSome]
  rfl

theorem frames_skel (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) :
    (partsAt T B).frames.map (fun x => (x.1, skel x.2)) =
      framesSk B.shape (T.lots.map (lotSk B.G₀)) := by
  unfold framesSk
  show (B.all.flatMap _).map _ = _
  rw [hB, List.flatMap_map, List.flatMap_map, List.map_flatMap]
  refine List.flatMap_congr fun L _ => ?_
  show List.map _ (if L.letters = true then [] else _) = if L.letters = true then [] else _
  cases L.letters with
  | true => rfl
  | false =>
    show List.map _ (List.filterMap _ _) =
      List.filterMap _ (List.filter _ ((L.blocks B.G₀).map skel))
    rw [filter_skel, List.filterMap_map, List.map_filterMap]
    refine List.filterMap_congr fun b _ => ?_
    show Option.map _ (match roleOf B.shape b.place with
      | .common => none
      | .stray => none
      | r => some (r, guardMark b)) = (match roleOf B.shape b.place with
      | .common => none
      | .stray => none
      | r => some (r, skel b))
    cases roleOf B.shape b.place <;> rfl

theorem here_skel (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) (a : Place) :
    ((T.lots.map (lotSk B.G₀)).filterMap fun L =>
      (L.blocks.find? fun b => b.place == a).map fun b => (L, b)) =
    (B.all.filterMap fun x => (x.2.find? fun b => b.place == a).map fun b => (x.1, b)).map
      fun x => (lotSk B.G₀ x.1, skel x.2) := by
  rw [hB, List.filterMap_map, List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun L _ => ?_
  show Option.map _ (((L.blocks B.G₀).map skel).find? fun b => b.place == a) = _
  rw [find_skel]
  show Option.map _ (Option.map skel ((L.blocks B.G₀).find? fun b => b.place == a)) =
    Option.map _ (Option.map _ ((L.blocks B.G₀).find? fun b => b.place == a))
  cases (L.blocks B.G₀).find? fun b => b.place == a <;> rfl

/-- One place's verdict, in skeletons. -/
theorem place_case (G : Ground) (face : Option (Block S ProofFile.Cl))
    (here : List (Lot × Block S ProofFile.Cl)) (looks : List String) (name : String) :
    Except.map skel
      (match face, here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => .ok f
      | none, some x => .ok { guardMark x.2 with name := name }
      | none, none =>
        match here with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here")) =
      (match face.map skel, (here.map fun x => (lotSk G x.1, skel x.2)).find? fun x =>
          !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => .ok f
      | none, some x => .ok { x.2 with name := name }
      | none, none =>
        match here.map fun x => (lotSk G x.1, skel x.2) with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here")) := by
  have e : ((here.map fun x => (lotSk G x.1, skel x.2)).find? fun x =>
      !x.1.letters && !(looks.any x.1.still.contains)) =
      (here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains)).map
        fun x => (lotSk G x.1, skel x.2) := by
    rw [List.find?_map]
    rfl
  rw [e]
  cases face with
  | some f => rfl
  | none =>
    cases here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
    | some x => rfl
    | none => cases here <;> rfl

/-- **T16, the places.** -/
theorem places_skel (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) :
    (partsAt T B).places.map (fun x => (x.1, x.2.map skel)) =
      placesSk B.spots (T.lots.map (lotSk B.G₀)) := by
  unfold placesSk
  show (B.spots.map _).map _ = _
  rw [List.map_map]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext rfl ?_
  have hf : (((partsAt T B).road.batch p.place).map fun mk => mk fun s => .ok ([], s)).map skel =
      roadSk B.spots (T.lots.map (lotSk B.G₀)) p.place := by
    rw [Option.map_map]
    exact road_triv T B p.place
  dsimp only
  rw [here_skel T B hB p.place, ← hf]
  exact place_case B.G₀ _ _ (p.cuts.flatMap fun c => [stepName c.look, c.look]) p.name

end

/-! ### lackingAt -/

/-- `lackingAt` on skeletons. -/
def lackingSk (places : List (Spot × Except String Skel)) (roles : List FrameRole)
    (onRoad eachAt testsAt : List Nat) (shared second : Option (String × List String)) :
    List String :=
  let links := (places.filterMap fun x => x.1.place.link).eraseDups
  let first := places.filterMap fun x =>
    match x.2 with
    | .ok _ => none
    | .error why =>
      some (s!"{x.1.name} ({kindWord x.1.place.kind})" ++ (if why.isEmpty then "" else ": " ++ why))
  let firstAt := fun (l : Nat) =>
    (places.find? fun x => x.1.place.link == some l && x.1.place.piece == 1).map (·.1.name)
  let has := fun (r : FrameRole) => roles.contains r
  let enters := fun (l : Nat) => places.any fun x =>
    x.1.place.link == some l && x.1.place.piece == 1 && x.1.cuts.any fun c => isFrameStep x.1 c.look
  let opened := fun (l : Nat) =>
    !enters l ||
      match firstAt l with
      | some n => has (.behind l n)
      | none => false
  let frames := links.flatMap fun l =>
    (if has (.lay l) then [] else [s!"link {l}: laid (frame)"]) ++
    (if opened l then [] else [s!"link {l}: opened (frame)"]) ++
    (if has (.clear l) then [] else [s!"link {l}: cleared (frame)"]) ++
    (if onRoad.contains l then [] else [s!"link {l}: the batching as a function (K9)"]) ++
    (if eachAt.contains l then [] else [s!"link {l}: Link.each (K9)"]) ++
    (if testsAt.contains l then [] else [s!"link {l}: Link.tests (K9)"])
  let later := fun (what : String) (lot : Option (String × List String)) =>
    match lot with
    | none => [what ++ " (the whole chain)"]
    | some x => x.2.map fun n =>
      s!"{n} ({what}: still runs the older verifier, by the statement of {x.1})"
  first ++ frames ++ later "the shared chain" shared ++ later "the second chain" second

/-- **T17.** General in the parts. -/
theorem lackingAt_skel (T : PureSeat) (P : PureParts) :
    lackingAt T P =
      lackingSk (P.places.map fun x => (x.1, x.2.map skel)) (P.frames.map (·.1)) P.onRoad P.eachAt
        P.testsAt (T.shared.map fun A => (A.lot, A.standIns))
        (T.second.map fun B => (B.lot, B.standIns)) := by
  unfold lackingAt lackingSk
  simp only [List.filterMap_map, List.find?_map, List.any_map, Function.comp_def, Option.map_map]
  congr 3
  refine List.filterMap_congr fun x _ => ?_
  cases x.2 <;> rfl

/-- **The blocks at the places**: `base` returns just where the places' skeletons all stand. -/
theorem base_skel (P : PureParts) :
    P.base.map (List.map skel) = (P.places.map fun x => (x.1, x.2.map skel)).mapM fun x => x.2 := by
  unfold PureParts.base
  rw [mapM_ok, List.mapM_map]
  rfl

end ProofFile.Sk

#print axioms ProofFile.Sk.isSome_findSome
#print axioms ProofFile.Sk.map_findSome
#print axioms ProofFile.Sk.mapM_ok
#print axioms ProofFile.Sk.skel_guardMark
#print axioms ProofFile.Sk.quiet_skel
#print axioms ProofFile.Sk.maker_skel
#print axioms ProofFile.Sk.road_skel
#print axioms ProofFile.Sk.road_triv
#print axioms ProofFile.Sk.onRoad_skel
#print axioms ProofFile.Sk.eachAt_skel
#print axioms ProofFile.Sk.testsAt_skel
#print axioms ProofFile.Sk.frames_skel
#print axioms ProofFile.Sk.here_skel
#print axioms ProofFile.Sk.place_case
#print axioms ProofFile.Sk.places_skel
#print axioms ProofFile.Sk.lackingAt_skel
#print axioms ProofFile.Sk.base_skel
