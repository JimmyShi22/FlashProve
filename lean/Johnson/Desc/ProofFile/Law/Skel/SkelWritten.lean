-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelWritten.lean: A LOT's SKELETON AS PLAIN DATA. Definitions,
statements and proofs.
Why. `LotSk.batch` is a function of every place. A lot's own text may answer at places that the
description never asks (K9's lot tests a place's kind, segment and piece, not its chain), so "this
lot's skeleton is the written one" cannot be an equation of functions with a table. The texts on
skeletons ask `batch` at the places of the list of places, at the batchings' places, and at the
places at which the driver asks for a segment's batching.
  `a9Of x`: the place at which the driver asks for the batching of segment x.2, of the sort x.1
  `linkAtSk_congr`, `bareChainSk_congr`, `chainCSk_congr`, `chainBySk_congr`: the driver's texts on
    skeletons read the batchings at these places alone
  `LotSk.cutB as k`: k, with "none" outside as in `batch`. `makerSk_cutB` … `faultsSk_cutB`
  `LotW`: name, `letters`, `still`, the blocks' skeletons, the batchings' skeletons as a list over
    places, the numbers at which `each` is supplied, those at which `tests` is. `LotW.sk`: as a
    `LotSk`. `lotW as ls k`: the plain data of k at the places as and the numbers ls
  `sk_lotW`: `(lotW as ls k).sk = (k.cut ls).cutB as`
  `back_of_written`: `back_of_skel` (SkelEnd.lean) with one equation of plain data for the lots
Limits. As SkelEnd.lean's: no premise is paid. A SKELETON IS BLIND, BY ITS MAKE, to a block's
decision, to its runs of claims but for their names, to its rounds' entries (it holds how many), and
to the guards (`skel_guarded`, `skel_guardMark`: a block has one skeleton with and without them): so
an equation of skeletons says nothing on what a block tests. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-! ### the driver's texts read the batchings at the ninth places alone -/

/-- The place at which the driver asks for a segment's batching. -/
def a9Of (x : ModelPart × Nat) : Place :=
  { chain := 1, link := some x.2, piece := (kindsBeforeBatching x.1 (x.2 == 0)).length + 1, kind := .K9 }

theorem mapM_congr_mem {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_congr_mem f g l fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem blockAtSk_congr (H H' : BlocksSk) (hb : H.block = H'.block) :
    blockAtSk H = blockAtSk H' := by
  funext a
  unfold blockAtSk
  rw [hb]

theorem linkAtSk_congr (H H' : BlocksSk) (hb : H.block = H'.block) (l : Nat) (sub : ModelPart)
    (h9 : H.batch (a9Of (sub, l)) = H'.batch (a9Of (sub, l))) :
    linkAtSk H l sub = linkAtSk H' l sub := by
  have h9' : H.batch
      { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 } =
      H'.batch
      { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 } :=
    h9
  unfold linkAtSk
  dsimp only
  rw [blockAtSk_congr H H' hb, h9']

theorem bareChainSk_congr (H H' : BlocksSk) (hb : H.block = H'.block) (hf : H.first = H'.first)
    (hl : H.last = H'.last) (links : List ModelPart) (several : Bool)
    (h9 : ∀ x ∈ links.zipIdx, H.batch (a9Of x) = H'.batch (a9Of x)) :
    bareChainSk H links several = bareChainSk H' links several := by
  unfold bareChainSk
  rw [mapM_congr_mem (fun x : ModelPart × Nat => linkAtSk H x.2 x.1) (fun x => linkAtSk H' x.2 x.1) _
    fun x hx => linkAtSk_congr H H' hb x.2 x.1 (h9 x hx), blockAtSk_congr H H' hb, hf, hl]

theorem chainCSk_congr (bs : List Skel) (links : List ModelPart) (kb kb' : Place → Option Skel)
    (first : Skel) (h : ∀ x ∈ links.zipIdx, kb (a9Of x) = kb' (a9Of x)) :
    chainCSk bs links kb first = chainCSk bs links kb' first := by
  unfold chainCSk
  cases bs.getLast? with
  | none => rfl
  | some z =>
    dsimp only
    rw [bareChainSk_congr (fillSk bs.dropLast z kb first) (fillSk bs.dropLast z kb' first) rfl rfl
      rfl links _ fun x hx => by
        show (kb (a9Of x) <|> _) = (kb' (a9Of x) <|> _)
        rw [h x hx]]

theorem chainBySk_congr (subs : List ModelPart) (base : List Skel) (fr : List (FrameRole × Skel))
    (kb kb' : Place → Option Skel) (h : ∀ x ∈ subs.zipIdx, kb (a9Of x) = kb' (a9Of x)) :
    chainBySk subs base fr kb = chainBySk subs base fr kb' := by
  unfold chainBySk
  exact chainCSk_congr _ subs kb kb' _ h

/-! ### batch, cut to a list of places -/

/-- k, with "none" outside as in `batch`. -/
def LotSk.cutB (as : List Place) (k : LotSk) : LotSk :=
  { k with batch := fun a => if as.contains a then k.batch a else none }

theorem batch_cutB (as : List Place) (a : Place) (h : a ∈ as) (k : LotSk) :
    (k.cutB as).batch a = k.batch a := by
  have hc : as.contains a = true := List.elem_iff.2 h
  show (if as.contains a = true then k.batch a else none) = k.batch a
  rw [if_pos hc]

section
variable (as : List Place) (ks : List LotSk)

theorem quiet_cutB :
    ((ks.map (LotSk.cutB as)).filter fun L => !L.letters) =
      (ks.filter fun L => !L.letters).map (LotSk.cutB as) := by
  rw [List.filter_map]
  rfl

theorem makerSk_cutB (a : Place) (h : a ∈ as) :
    makerSk (ks.map (LotSk.cutB as)) a = makerSk ks a := by
  unfold makerSk
  rw [quiet_cutB, List.findSome?_map]
  exact congrArg (fun f => List.findSome? f _) (funext fun k => batch_cutB as a h k)

theorem roadSk_cutB (spots : List Spot) (a : Place) (h : a ∈ as) :
    roadSk spots (ks.map (LotSk.cutB as)) a = roadSk spots ks a := by
  unfold roadSk
  rw [makerSk_cutB as ks a h]

theorem onRoadSk_cutB (batchAt : List (Nat × Place)) (h : ∀ x ∈ batchAt, x.2 ∈ as) :
    onRoadSk batchAt (ks.map (LotSk.cutB as)) = onRoadSk batchAt ks := by
  unfold onRoadSk
  refine List.filterMap_congr fun x hx => ?_
  rw [makerSk_cutB as ks x.2 (h x hx)]

theorem framesSk_cutB (shape : List (String × Place)) :
    framesSk shape (ks.map (LotSk.cutB as)) = framesSk shape ks := by
  unfold framesSk
  rw [List.flatMap_map]
  rfl

theorem eachAtSk_cutB (spots : List Spot) :
    eachAtSk spots (ks.map (LotSk.cutB as)) = eachAtSk spots ks := by
  unfold eachAtSk
  simp only [quiet_cutB, List.any_map, Function.comp_def]
  rfl

theorem testsAtSk_cutB (spots : List Spot) :
    testsAtSk spots (ks.map (LotSk.cutB as)) = testsAtSk spots ks := by
  unfold testsAtSk
  simp only [quiet_cutB, List.any_map, Function.comp_def]
  rfl

theorem here_cutB (a : Place) :
    ((ks.map (LotSk.cutB as)).filterMap fun L =>
      (L.blocks.find? fun b => b.place == a).map fun b => (L, b)) =
    (ks.filterMap fun L => (L.blocks.find? fun b => b.place == a).map fun b => (L, b)).map
      fun x => (x.1.cutB as, x.2) := by
  rw [List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun L _ => ?_
  show Option.map _ (L.blocks.find? fun b => b.place == a) =
    Option.map _ (Option.map _ (L.blocks.find? fun b => b.place == a))
  cases L.blocks.find? fun b => b.place == a <;> rfl

theorem place_cutB (fk : Option Skel) (here : List (LotSk × Skel)) (looks : List String)
    (name : String) :
    (match fk, (here.map fun (x : LotSk × Skel) => (x.1.cutB as, x.2)).find? fun x =>
          !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => (.ok f : Except String Skel)
      | none, some x => .ok { x.2 with name := name }
      | none, none =>
        match here.map fun (x : LotSk × Skel) => (x.1.cutB as, x.2) with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here")) =
      (match fk, here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => .ok f
      | none, some x => .ok { x.2 with name := name }
      | none, none =>
        match here with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here")) := by
  have e : ((here.map fun (x : LotSk × Skel) => (x.1.cutB as, x.2)).find? fun x =>
      !x.1.letters && !(looks.any x.1.still.contains)) =
      (here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains)).map
        fun x => (x.1.cutB as, x.2) := by
    rw [List.find?_map]
    rfl
  rw [e]
  cases fk with
  | some f => rfl
  | none =>
    cases here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
    | some x => rfl
    | none => cases here <;> rfl

theorem placesSk_cutB (spots : List Spot) (h : ∀ p ∈ spots, p.place ∈ as) :
    placesSk spots (ks.map (LotSk.cutB as)) = placesSk spots ks := by
  unfold placesSk
  refine List.map_congr_left fun p hp => ?_
  refine Prod.ext rfl ?_
  dsimp only
  rw [roadSk_cutB as ks spots p.place (h p hp), here_cutB]
  exact place_cutB as _ _ (p.cuts.flatMap fun c => [stepName c.look, c.look]) p.name

theorem faultsSk_cutB (spots : List Spot) (shape : List (String × Place))
    (batchAt : List (Nat × Place)) (h : ∀ p ∈ spots, p.place ∈ as)
    (h' : ∀ x ∈ batchAt, x.2 ∈ as) :
    faultsSk spots shape batchAt (ks.map (LotSk.cutB as)) = faultsSk spots shape batchAt ks := by
  have hb : ((ks.map (LotSk.cutB as)).flatMap fun L => L.blocks) =
      ks.flatMap fun L => L.blocks := by
    rw [List.flatMap_map]
    rfl
  have hg : ∀ a ∈ as, ((ks.map (LotSk.cutB as)).filter fun L => (L.batch a).isSome) =
      (ks.filter fun L => (L.batch a).isSome).map (LotSk.cutB as) := by
    intro a ha
    rw [List.filter_map]
    exact congrArg (fun f => List.map _ (List.filter f ks))
      (funext fun k => by show ((k.cutB as).batch a).isSome = _; rw [batch_cutB as a ha])
  have hy : ∀ a ∈ as, ((ks.map (LotSk.cutB as)).any fun L => (L.batch a).isSome) =
      ks.any fun L => (L.batch a).isSome := by
    intro a ha
    rw [List.any_map]
    exact congrArg (fun f => List.any ks f)
      (funext fun k => by show ((k.cutB as).batch a).isSome = _; rw [batch_cutB as a ha])
  have hr : (batchAt.filterMap fun x =>
      if (ks.map (LotSk.cutB as)).any fun L => (L.batch x.2).isSome then some x.1 else none) =
      batchAt.filterMap fun x =>
        if ks.any fun L => (L.batch x.2).isSome then some x.1 else none :=
    List.filterMap_congr fun x hx => by rw [hy x.2 (h' x hx)]
  unfold faultsSk
  dsimp only
  rw [hb, hr]
  congr 1
  · congr 2
    refine List.flatMap_congr fun p hp => ?_
    rw [hg p.place (h p hp)]
    simp only [List.isEmpty_map, List.any_map, List.length_map, Function.comp_def,
      batch_cutB as p.place (h p hp)]
    rfl
  · refine List.flatMap_congr fun l _ => ?_
    simp only [List.filter_map, List.any_map, List.length_map, Function.comp_def]
    rfl

end

/-! ### plain data -/

/-- **A lot's skeleton as plain data.** -/
structure LotW where
  name : String
  letters : Bool
  still : List String
  blocks : List Skel
  batch : List (Place × Skel)
  each : List Nat
  tests : List Nat
  deriving DecidableEq, Repr

/-- As a `LotSk`. -/
def LotW.sk (w : LotW) : LotSk :=
  { name := w.name, letters := w.letters, still := w.still, blocks := w.blocks
    batch := fun a => w.batch.lookup a, each := fun l => w.each.contains l
    tests := fun l => w.tests.contains l }

/-- The plain data of k at the places as and the numbers ls. -/
def lotW (as : List Place) (ls : List Nat) (k : LotSk) : LotW :=
  { name := k.name, letters := k.letters, still := k.still, blocks := k.blocks
    batch := as.filterMap fun a => (k.batch a).map fun s => (a, s)
    each := ls.filter k.each, tests := ls.filter k.tests }

theorem lookup_asked (f : Place → Option Skel) (a : Place) :
    ∀ as : List Place, (as.filterMap fun b => (f b).map fun s => (b, s)).lookup a =
      if as.contains a then f a else none
  | [] => rfl
  | b :: as => by
    have ih := lookup_asked f a as
    by_cases hab : a = b
    · subst hab
      cases hf : f a with
      | none =>
        rw [List.filterMap_cons_none (by rw [hf]; rfl), ih]
        simp [hf]
      | some s =>
        rw [List.filterMap_cons_some (by rw [hf]; rfl)]
        simp
    · have hne : (a == b) = false := by simpa using hab
      cases hf : f b with
      | none =>
        rw [List.filterMap_cons_none (by rw [hf]; rfl), ih]
        simp [hab]
      | some s =>
        rw [List.filterMap_cons_some (by rw [hf]; rfl), List.lookup_cons, hne, ih]
        simp [hab]

theorem contains_filter (p : Nat → Bool) (ls : List Nat) (l : Nat) :
    (ls.filter p).contains l = (ls.contains l && p l) := by
  by_cases h : l ∈ ls <;> cases hp : p l <;> simp [List.mem_filter, h, hp]

theorem sk_lotW (as : List Place) (ls : List Nat) (k : LotSk) :
    (lotW as ls k).sk = (k.cut ls).cutB as := by
  unfold LotW.sk lotW LotSk.cutB LotSk.cut
  simp only [LotSk.mk.injEq, true_and]
  exact ⟨funext fun a => lookup_asked k.batch a as, funext fun l => contains_filter k.each ls l,
    funext fun l => contains_filter k.tests ls l⟩

/-- The places at which the texts on skeletons ask `batch`, each once. -/
def askedOf (spots : List Spot) (batchAt : List (Nat × Place)) (subs : List ModelPart) : List Place :=
  (spots.map (·.place) ++ batchAt.map (·.2) ++ subs.zipIdx.map a9Of).eraseDups

/-- **`back_of_skel` with one equation of plain data for the lots.** -/
theorem back_of_written (Z : Pub) (T : PureSeat) (B : PureBase) (ws : List LotW)
    (bl fl : List Skel)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hk : (T.lots.map (lotSk B.G₀)).map
      (lotW (askedOf B.spots B.batchAt (subsOf Z)) (linksOf B.spots)) = ws)
    (hS : ∀ L ∈ T.lots, Steady B.G₀ L)
    (c₂ : faultsSk B.spots B.shape B.batchAt (ws.map LotW.sk) = [])
    (c₃ : lackingSk (placesSk B.spots (ws.map LotW.sk))
      ((framesSk B.shape (ws.map LotW.sk)).map (·.1)) (onRoadSk B.batchAt (ws.map LotW.sk))
      (eachAtSk B.spots (ws.map LotW.sk)) (testsAtSk B.spots (ws.map LotW.sk))
      (T.shared.map fun A => (A.lot, A.standIns)) (T.second.map fun A => (A.lot, A.standIns)) = [])
    (c₄ : ((placesSk B.spots (ws.map LotW.sk)).mapM fun x => x.2) = .ok bl)
    (c₅ : chainBySk (subsOf Z) bl (framesSk B.shape (ws.map LotW.sk))
      (roadSk B.spots (ws.map LotW.sk)) = .ok fl) :
    faultsAt T B = [] ∧ lackingAt T (partsAt T B) = [] ∧
      ∃ base, (partsAt T B).base = .ok base ∧ base.map skel = bl ∧
        ∃ c, chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
          c.blocksInOrder.map skel = fl := by
  subst hk
  have hw : ((T.lots.map (lotSk B.G₀)).map
      (lotW (askedOf B.spots B.batchAt (subsOf Z)) (linksOf B.spots))).map LotW.sk =
      (((T.lots.map (lotSk B.G₀)).map (LotSk.cut (linksOf B.spots))).map
        (LotSk.cutB (askedOf B.spots B.batchAt (subsOf Z)))) := by
    simp only [List.map_map]
    exact List.map_congr_left fun L _ => sk_lotW _ _ (lotSk B.G₀ L)
  have h1 : ∀ p ∈ B.spots, p.place ∈ askedOf B.spots B.batchAt (subsOf Z) := fun p hp =>
    List.mem_eraseDups.2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hp)))
  have h2 : ∀ x ∈ B.batchAt, x.2 ∈ askedOf B.spots B.batchAt (subsOf Z) := fun x hx =>
    List.mem_eraseDups.2
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hx)))
  have h3 : ∀ x ∈ (subsOf Z).zipIdx, a9Of x ∈ askedOf B.spots B.batchAt (subsOf Z) := fun x hx =>
    List.mem_eraseDups.2 (List.mem_append_right _ (List.mem_map_of_mem hx))
  rw [hw] at c₂ c₃ c₄ c₅
  rw [faultsSk_cutB _ _ _ _ _ h1 h2] at c₂
  rw [placesSk_cutB _ _ _ h1, framesSk_cutB, onRoadSk_cutB _ _ _ h2, eachAtSk_cutB,
    testsAtSk_cutB] at c₃
  rw [placesSk_cutB _ _ _ h1] at c₄
  rw [framesSk_cutB, chainBySk_congr _ _ _ _ (roadSk B.spots
    ((T.lots.map (lotSk B.G₀)).map (LotSk.cut (linksOf B.spots)))) fun x hx =>
      roadSk_cutB _ _ _ _ (h3 x hx)] at c₅
  exact back_of_skel_cut Z T B _ bl fl hB rfl hS c₂ c₃ c₄ c₅

end ProofFile.Sk

#print axioms ProofFile.Sk.mapM_congr_mem
#print axioms ProofFile.Sk.blockAtSk_congr
#print axioms ProofFile.Sk.linkAtSk_congr
#print axioms ProofFile.Sk.bareChainSk_congr
#print axioms ProofFile.Sk.chainCSk_congr
#print axioms ProofFile.Sk.chainBySk_congr
#print axioms ProofFile.Sk.batch_cutB
#print axioms ProofFile.Sk.quiet_cutB
#print axioms ProofFile.Sk.makerSk_cutB
#print axioms ProofFile.Sk.roadSk_cutB
#print axioms ProofFile.Sk.onRoadSk_cutB
#print axioms ProofFile.Sk.framesSk_cutB
#print axioms ProofFile.Sk.eachAtSk_cutB
#print axioms ProofFile.Sk.testsAtSk_cutB
#print axioms ProofFile.Sk.here_cutB
#print axioms ProofFile.Sk.place_cutB
#print axioms ProofFile.Sk.placesSk_cutB
#print axioms ProofFile.Sk.faultsSk_cutB
#print axioms ProofFile.Sk.lookup_asked
#print axioms ProofFile.Sk.contains_filter
#print axioms ProofFile.Sk.sk_lotW
#print axioms ProofFile.Sk.back_of_written
