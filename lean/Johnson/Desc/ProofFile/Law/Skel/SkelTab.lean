-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelTab.lean: A LOT's SKELETON NEED SAY WHETHER IT SUPPLIES `each`
AND `tests` AT THE SEGMENTS' NUMBERS ALONE. Definitions, statements and proofs.
Why. `LotSk.each` and `LotSk.tests` are functions of every number, so a row "this lot's skeleton is
the written one" would be an equation at all numbers. The texts on skeletons ask them at the numbers
of the places' segments alone.
  `linksOf spots`: these numbers. `LotSk.cut ls k`: k, with "no" outside ls in both fields
  `makerSk_cut`, `roadSk_cut`, `onRoadSk_cut`, `framesSk_cut`, `placesSk_cut`: five texts do not
    read the two fields. `eachAtSk_cut`, `testsAtSk_cut`, `faultsSk_cut`: three read them inside
    `linksOf spots` alone
  `back_of_skel_cut`: `back_of_skel` (SkelEnd.lean) with the lots' skeletons cut
Limits. As SkelEnd.lean's: no premise is paid. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-- The numbers of the places' segments, each once. -/
def linksOf (spots : List Spot) : List Nat := (spots.filterMap fun p => p.place.link).eraseDups

/-- k, with "no" outside ls in `each` and `tests`. -/
def LotSk.cut (ls : List Nat) (k : LotSk) : LotSk :=
  { k with
    each := fun l => ls.contains l && k.each l
    tests := fun l => ls.contains l && k.tests l }

section
variable (ls : List Nat) (ks : List LotSk)

theorem quiet_cut :
    ((ks.map (LotSk.cut ls)).filter fun L => !L.letters) =
      (ks.filter fun L => !L.letters).map (LotSk.cut ls) := by
  rw [List.filter_map]
  rfl

theorem makerSk_cut (a : Place) : makerSk (ks.map (LotSk.cut ls)) a = makerSk ks a := by
  unfold makerSk
  rw [quiet_cut, List.findSome?_map]
  rfl

theorem roadSk_cut (spots : List Spot) :
    roadSk spots (ks.map (LotSk.cut ls)) = roadSk spots ks := by
  funext a
  unfold roadSk
  rw [makerSk_cut]

theorem onRoadSk_cut (batchAt : List (Nat × Place)) :
    onRoadSk batchAt (ks.map (LotSk.cut ls)) = onRoadSk batchAt ks := by
  unfold onRoadSk
  simp only [makerSk_cut]

theorem framesSk_cut (shape : List (String × Place)) :
    framesSk shape (ks.map (LotSk.cut ls)) = framesSk shape ks := by
  unfold framesSk
  rw [List.flatMap_map]
  rfl

theorem here_cut (a : Place) :
    ((ks.map (LotSk.cut ls)).filterMap fun L =>
      (L.blocks.find? fun b => b.place == a).map fun b => (L, b)) =
    (ks.filterMap fun L => (L.blocks.find? fun b => b.place == a).map fun b => (L, b)).map
      fun x => (x.1.cut ls, x.2) := by
  rw [List.filterMap_map, List.map_filterMap]
  refine List.filterMap_congr fun L _ => ?_
  show Option.map _ (L.blocks.find? fun b => b.place == a) =
    Option.map _ (Option.map _ (L.blocks.find? fun b => b.place == a))
  cases L.blocks.find? fun b => b.place == a <;> rfl

theorem place_cut (fk : Option Skel) (here : List (LotSk × Skel)) (looks : List String)
    (name : String) :
    (match fk, (here.map fun (x : LotSk × Skel) => (x.1.cut ls, x.2)).find? fun x =>
          !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => (.ok f : Except String Skel)
      | none, some x => .ok { x.2 with name := name }
      | none, none =>
        match here.map fun (x : LotSk × Skel) => (x.1.cut ls, x.2) with
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
  have e : ((here.map fun (x : LotSk × Skel) => (x.1.cut ls, x.2)).find? fun x =>
      !x.1.letters && !(looks.any x.1.still.contains)) =
      (here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains)).map
        fun x => (x.1.cut ls, x.2) := by
    rw [List.find?_map]
    rfl
  rw [e]
  cases fk with
  | some f => rfl
  | none =>
    cases here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
    | some x => rfl
    | none => cases here <;> rfl

theorem placesSk_cut (spots : List Spot) :
    placesSk spots (ks.map (LotSk.cut ls)) = placesSk spots ks := by
  unfold placesSk
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext rfl ?_
  dsimp only
  rw [roadSk_cut, here_cut]
  exact place_cut ls _ _ (p.cuts.flatMap fun c => [stepName c.look, c.look]) p.name

end

theorem any_cut (ls : List Nat) (ks : List LotSk) (l : Nat) (hl : l ∈ ls)
    (f : LotSk → Nat → Bool) (g : LotSk → Nat → Bool)
    (h : ∀ k, g (k.cut ls) l = (ls.contains l && f k l)) :
    ((ks.map (LotSk.cut ls)).any fun L => g L l) = ks.any fun L => f L l := by
  have hc : ls.contains l = true := List.elem_iff.2 hl
  rw [List.any_map]
  refine congrArg (fun p => ks.any p) (funext fun k => ?_)
  show g (k.cut ls) l = f k l
  rw [h, hc, Bool.true_and]

theorem eachAtSk_cut (spots : List Spot) (ks : List LotSk) :
    eachAtSk spots (ks.map (LotSk.cut (linksOf spots))) = eachAtSk spots ks := by
  unfold eachAtSk
  refine List.filter_congr fun l hl => ?_
  rw [quiet_cut]
  exact any_cut (linksOf spots) _ l hl (fun k l => k.each l) (fun k l => k.each l) fun _ => rfl

theorem testsAtSk_cut (spots : List Spot) (ks : List LotSk) :
    testsAtSk spots (ks.map (LotSk.cut (linksOf spots))) = testsAtSk spots ks := by
  unfold testsAtSk
  refine List.filter_congr fun l hl => ?_
  rw [quiet_cut]
  exact any_cut (linksOf spots) _ l hl (fun k l => k.tests l) (fun k l => k.tests l) fun _ => rfl

theorem count_cut (ls : List Nat) (ks : List LotSk) (l : Nat) (hl : l ∈ ls)
    (f : LotSk → Nat → Bool) (h : ∀ k, f (k.cut ls) l = (ls.contains l && f k l)) :
    ((ks.map (LotSk.cut ls)).filter fun L => f L l).length = (ks.filter fun L => f L l).length := by
  have hc : ls.contains l = true := List.elem_iff.2 hl
  rw [List.filter_map, List.length_map]
  refine congrArg (fun p => (ks.filter p).length) (funext fun k => ?_)
  show f (k.cut ls) l = f k l
  rw [h, hc, Bool.true_and]

theorem faultsSk_cut (spots : List Spot) (shape : List (String × Place))
    (batchAt : List (Nat × Place)) (ks : List LotSk) :
    faultsSk spots shape batchAt (ks.map (LotSk.cut (linksOf spots))) =
      faultsSk spots shape batchAt ks := by
  have hb : ((ks.map (LotSk.cut (linksOf spots))).flatMap fun L => L.blocks) =
      ks.flatMap fun L => L.blocks := by
    rw [List.flatMap_map]
    rfl
  have hg : ∀ a : Place, ((ks.map (LotSk.cut (linksOf spots))).filter fun L =>
      (L.batch a).isSome) = (ks.filter fun L => (L.batch a).isSome).map
        (LotSk.cut (linksOf spots)) := by
    intro a
    rw [List.filter_map]
    rfl
  have ha : ∀ a : Place, ((ks.map (LotSk.cut (linksOf spots))).any fun L => (L.batch a).isSome) =
      ks.any fun L => (L.batch a).isSome := by
    intro a
    rw [List.any_map]
    rfl
  unfold faultsSk
  dsimp only
  rw [hb]
  simp only [hg, ha, List.isEmpty_map, List.any_map, List.length_map, Function.comp_def]
  congr 1
  refine List.flatMap_congr fun l hl => ?_
  have e1 : ((ks.map (LotSk.cut (linksOf spots))).filter fun L => L.each l).length =
      (ks.filter fun L => L.each l).length :=
    count_cut (linksOf spots) ks l hl (fun k l => k.each l) fun _ => rfl
  have e2 : ((ks.map (LotSk.cut (linksOf spots))).filter fun L => L.tests l).length =
      (ks.filter fun L => L.tests l).length :=
    count_cut (linksOf spots) ks l hl (fun k l => k.tests l) fun _ => rfl
  have hc : (linksOf spots).contains l = true := List.elem_iff.2 hl
  simp only [e1, e2, LotSk.cut, hc, Bool.true_and]

/-- **`back_of_skel` with the lots' skeletons cut to the segments' numbers.** -/
theorem back_of_skel_cut (Z : Pub) (T : PureSeat) (B : PureBase) (ks : List LotSk)
    (bl fl : List Skel)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hk : (T.lots.map (lotSk B.G₀)).map (LotSk.cut (linksOf B.spots)) = ks)
    (hS : ∀ L ∈ T.lots, Steady B.G₀ L)
    (c₂ : faultsSk B.spots B.shape B.batchAt ks = [])
    (c₃ : lackingSk (placesSk B.spots ks) ((framesSk B.shape ks).map (·.1))
      (onRoadSk B.batchAt ks) (eachAtSk B.spots ks) (testsAtSk B.spots ks)
      (T.shared.map fun A => (A.lot, A.standIns)) (T.second.map fun A => (A.lot, A.standIns)) = [])
    (c₄ : ((placesSk B.spots ks).mapM fun x => x.2) = .ok bl)
    (c₅ : chainBySk (subsOf Z) bl (framesSk B.shape ks) (roadSk B.spots ks) = .ok fl) :
    faultsAt T B = [] ∧ lackingAt T (partsAt T B) = [] ∧
      ∃ base, (partsAt T B).base = .ok base ∧ base.map skel = bl ∧
        ∃ c, chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
          c.blocksInOrder.map skel = fl := by
  subst hk
  rw [faultsSk_cut] at c₂
  rw [placesSk_cut, framesSk_cut, onRoadSk_cut, eachAtSk_cut, testsAtSk_cut] at c₃
  rw [placesSk_cut] at c₄
  rw [framesSk_cut, roadSk_cut] at c₅
  exact back_of_skel Z T B _ bl fl hB rfl hS c₂ c₃ c₄ c₅

end ProofFile.Sk

#print axioms ProofFile.Sk.quiet_cut
#print axioms ProofFile.Sk.makerSk_cut
#print axioms ProofFile.Sk.roadSk_cut
#print axioms ProofFile.Sk.onRoadSk_cut
#print axioms ProofFile.Sk.framesSk_cut
#print axioms ProofFile.Sk.here_cut
#print axioms ProofFile.Sk.place_cut
#print axioms ProofFile.Sk.placesSk_cut
#print axioms ProofFile.Sk.any_cut
#print axioms ProofFile.Sk.eachAtSk_cut
#print axioms ProofFile.Sk.testsAtSk_cut
#print axioms ProofFile.Sk.count_cut
#print axioms ProofFile.Sk.faultsSk_cut
#print axioms ProofFile.Sk.back_of_skel_cut
