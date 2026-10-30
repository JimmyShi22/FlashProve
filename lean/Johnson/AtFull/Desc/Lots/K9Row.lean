-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K9Row.lean: THE ROW OF KIND K9's LOT (ProofFile.k9Ninth,
  Johnson/Desc/ProofFile/Lot/K9.lean: the batching at the gatherer; each; tests;
  the closing as three blocks)
  FOR "onlineDescription's back reads a block's skeleton alone"
  (ProofFile.Sk.back_of_skel | back_of_skel_cut, Johnson/Desc/ProofFile/Law/Skel/):
  PART 1: THE GENERAL LAWS, AT EVERY PUBLIC PART Z AND EVERY GROUND G:
  no scope, no opening, no written value.
  Definitions with code, statements and proofs.

WHY. back_of_skel asks "steady" of every lot. A lot that supplies no batching is steady for nothing
  (steady_none, SkelEnd.lean); by report (not read at the other lots'
  texts) K9's is the one lot that supplies a batching as a function of the gatherer: here it is
  shown steady. And its skeleton is wanted as a term that reads of Z just what the lot reads.

THE NAMES.
batchSk p, closeSk p P, refuserSk: the skeletons of K9.batch atS p g (at every gatherer g), of
  K9.closeOf p P (the one equation, the closing, "shut") and of a block that refuses.
told_empty, skel_batch, skel_closeOf, skel_refuser: that they are these.
k10ParG: ProofFile.k10Par's text at the list of groups that it reads of Z (Z.s₀.check.frame.groups).
  k10Par_eq: by definition.
k9Ws, k9CloseAt, k9CloseSkAt, k9BlocksSk, k9BatchSk, k9Sk: the lot's own text, and that text on
  skeletons, as a function of the groups, the stretches and one Bool a segment.
k9CloseAt_skel, k9_own, k9_blocks, k9_batch_is, k9_batch_form, k9_batch, k9_each, k9_tests: field by
  field.
k9_steady: **ProofFile.Sk.Steady G (k9Ninth Z)**: the batching's skeleton is the same at every gatherer.
k9_row: **ProofFile.Sk.lotSk G (k9Ninth Z) = k9Sk Z.s₀.check.frame.groups (k9Stretches Z) (fun l =>
  (K9.testsWhere Z.p.X l 0).isSome).**

WHAT THE LOT READS OF Z, BY THAT EQUATION: Z.s₀.check.frame.groups · k9Stretches Z (that is: Z.cuts
  and Z.D.1) · whether K9.testsWhere Z.p.X l 0 returns. OF G: NOTHING.
Limits. Equations of terms: nothing is shown to return, to be true or to be the written value
  anywhere. Where a number cannot be read the lot lays a block that refuses: so does the twin.
  Nothing on soundness.
-/
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.Desc.ProofFile.Law.Skel.SkelParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.Lots
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (Where atS)
open ProofFile ProofFile.Sk

/-! ### the makers' skeletons -/

/-- The batching's skeleton. -/
def batchSk (p : Where) : Skel :=
  { name := "K9: the batching draw", place := ⟨p.chain, some p.link, p.piece, .K9⟩, nRounds := 1
    nOracles := 1, told := [], before := (List.range p.sent).map fun n => (p.chain, n)
    planOk := p.rows != 0, claims := [], after := [] }

/-- The skeletons of the three blocks that close a segment. -/
def closeSk (p : Where) (P : Par) : List Skel :=
  [{ name := "K9: the one equation", place := ⟨p.chain, some p.link, p.pieceEq, .K9⟩, nRounds := 0
     nOracles := 0, told := [], before := [], planOk := K9.fits p P, claims := [], after := [] },
   { name := s!"the closing of link {P.link}", place := ⟨1, some P.link, P.piece, .K10⟩
     nRounds := P.k + 2, nOracles := P.k + 2, told := [], before := P.sent.map fun n => (1, n)
     planOk := decide (1 ≤ P.k) && decide (P.h ≤ P.k), claims := [], after := [] },
   { name := "K9: the segment is shut", place := ⟨p.chain, some p.link, P.piece + 1, .K9⟩
     nRounds := 0, nOracles := 0, told := [], before := [], planOk := true, claims := []
     after := [] }]

/-- The skeleton of a block that refuses. -/
def refuserSk (name : String) (a : Place) : Skel :=
  { Skel.quiet name a.chain a.link a.piece with place := a, planOk := false }

/-- Rounds that send no root tell nothing. -/
theorem told_empty {α : Type} (l : List α) :
    ∀ k, toldFrom k (l.map fun _ => ([] : List Oracle)) = [] := by
  induction l with
  | nil => intro k; rfl
  | cons a l ih =>
    intro k
    show toldFrom k ([] :: l.map fun _ => ([] : List Oracle)) = []
    unfold toldFrom
    exact ih (k + 1)

theorem skel_batch (p : Where) (g : S → Except String (List Claim × S)) :
    skel (K9.batch atS p g) = batchSk p := rfl

theorem skel_closeOf (p : Where) (P : Par) :
    (K9.closeOf (Cl := Unit) p P).map skel = closeSk p P := by
  have e : (First.Close.entries P).length = P.k + 2 := by
    simp [First.Close.entries]
  have t := told_empty (First.Close.entries P) 0
  simp only [K9.closeOf, closeSk, List.map_cons, List.map_nil]
  refine congrArg₂ List.cons rfl (congrArg₂ List.cons ?_ rfl)
  show ({ name := s!"the closing of link {P.link}", place := ⟨1, some P.link, P.piece, .K10⟩
          nRounds := ((First.Close.entries P).map fun e => ({ entry := e } : Fmt.DeclaredRound)).length
          nOracles := ((First.Close.entries P).map fun _ => ([] : List Oracle)).length
          told := toldFrom 0 ((First.Close.entries P).map fun _ => ([] : List Oracle))
          before := P.sent.map fun n => (1, n)
          planOk := decide (1 ≤ P.k) && decide (P.h ≤ P.k), claims := [], after := [] } : Skel) = _
  rw [t, List.length_map, List.length_map, e]

theorem skel_refuser (name : String) (a : Place) (what : String) :
    skel (refuser name a what) = refuserSk name a := rfl

/-! ### the lot's text on skeletons -/

/-- `ProofFile.k10Par` at the list of groups that it reads of Z. -/
def k10ParG (groups : Array OnBytes.ReqGroup) (xs : List (Spot × List Fmt.DeclaredRound × Nat))
    (p : Where) : Option Par :=
  (xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).bind fun x =>
    (groups[p.link]?).bind fun Gr =>
      match x.2.1 with
      | bat :: _ :: round :: _ =>
        some { link := p.link, piece := p.pieceEq + 1, k := Gr.k, h := Gr.h
               rows := bat.entry.rows, workField := bat.entry.work
               workClose := round.entry.work, sent := List.range x.2.2 }
      | _ => none

theorem k10Par_eq (Z : Pub) (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (p : Where) :
    k10Par Z xs p = k10ParG Z.s₀.check.frame.groups xs p := rfl

/-- The segments' numbers, each with K9's numbers there. -/
def k9Ws (xs : List (Spot × List Fmt.DeclaredRound × Nat)) : List (Nat × Option Where) :=
  (k9Links xs).map fun l => (l, k9Where xs l)

/-- One segment's closing blocks, as the lot lays them. -/
def k9CloseAt (groups : Array OnBytes.ReqGroup) (xs : List (Spot × List Fmt.DeclaredRound × Nat))
    (w : Nat × Option Where) : List (Block S Unit) :=
  match w.2.bind fun p => (k10ParG groups xs p).map fun P => (p, P) with
  | some (p, P) => K9.closeOf p P
  | none => [refuser s!"link {w.1}: the closing" ⟨1, some w.1, 0, .K10⟩ "K9's or K10's numbers"]

/-- Their skeletons, at the description's type of claims. -/
def k9CloseSkAt (groups : Array OnBytes.ReqGroup) (xs : List (Spot × List Fmt.DeclaredRound × Nat))
    (w : Nat × Option Where) : List Skel :=
  match w.2.bind fun p => (k10ParG groups xs p).map fun P => (p, P) with
  | some (p, P) => (closeSk p P).map Skel.retype
  | none => [(refuserSk s!"link {w.1}: the closing" ⟨1, some w.1, 0, .K10⟩).retype]

theorem k9CloseAt_skel (groups : Array OnBytes.ReqGroup)
    (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (w : Nat × Option Where) :
    ((k9CloseAt groups xs w).map fun b => skel (b.retype : Block S ProofFile.Cl)) =
      k9CloseSkAt groups xs w := by
  unfold k9CloseAt k9CloseSkAt
  cases w.2.bind fun p => (k10ParG groups xs p).map fun P => (p, P) with
  | none =>
    show [skel ((refuser _ _ _).retype : Block S ProofFile.Cl)] = _
    rw [skel_retype, skel_refuser]
  | some y =>
    show ((K9.closeOf y.1 y.2).map fun b => skel (b.retype : Block S ProofFile.Cl)) =
      (closeSk y.1 y.2).map Skel.retype
    rw [← skel_closeOf, List.map_map]
    exact List.map_congr_left fun b _ => skel_retype b

/-- The lot's blocks' skeletons. -/
def k9BlocksSk (groups : Array OnBytes.ReqGroup) (xs : List (Spot × List Fmt.DeclaredRound × Nat)) :
    List Skel :=
  (k9Ws xs).flatMap (k9CloseSkAt groups xs)

theorem k9_own (Z : Pub) (G : Ground) :
    (k9Ninth Z).own G = (k9Ws (k9Stretches Z)).flatMap
      (k9CloseAt Z.s₀.check.frame.groups (k9Stretches Z)) := rfl

theorem k9_blocks (Z : Pub) (G : Ground) :
    ((k9Ninth Z).blocks G).map skel =
      k9BlocksSk Z.s₀.check.frame.groups (k9Stretches Z) := by
  have e : (k9Ninth Z).blocks G = ((k9Ninth Z).own G).map fun b => b.retype := by
    show ((k9Ninth Z).own G).map (fun b => b.retype) ++ [] = _
    rw [List.append_nil]
  rw [e, k9_own, List.map_map, List.map_flatMap]
  unfold k9BlocksSk
  exact congrArg (fun f => (k9Ws (k9Stretches Z)).flatMap f)
    (funext fun w => k9CloseAt_skel _ _ w)

/-- The field batch on skeletons. -/
def k9BatchSk (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (a : Place) : Option Skel :=
  match a.kind, a.link with
  | .K9, some l =>
    (((k9Ws xs).lookup l).bind id).bind fun p =>
      if p.piece == a.piece then some (batchSk p) else none
  | _, _ => none

/-- What the lot's batching is, where it supplies one. -/
theorem k9_batch_is (Z : Pub) (G : Ground) (a : Place) :
    (k9Ninth Z).batch G a =
      match a.kind, a.link with
      | .K9, some l =>
        (((k9Ws (k9Stretches Z)).lookup l).bind id).bind fun p =>
          if p.piece == a.piece then some fun g => K9.batch atS p g else none
      | _, _ => none := rfl

theorem k9_batch_form (Z : Pub) (G : Ground) (a : Place) (mk : Gatherer → Block S ProofFile.Cl)
    (h : (k9Ninth Z).batch G a = some mk) : ∃ p, mk = fun g => K9.batch atS p g := by
  rw [k9_batch_is] at h
  split at h
  · obtain ⟨p, -, hp⟩ := Option.bind_eq_some_iff.1 h
    split at hp
    · exact ⟨p, (Option.some.inj hp).symm⟩
    · cases hp
  · cases h

/-- **The batching's skeleton is the same at every gatherer.** -/
theorem k9_steady (Z : Pub) (G : Ground) : Steady G (k9Ninth Z) := by
  intro a mk h g g'
  obtain ⟨p, rfl⟩ := k9_batch_form Z G a mk h
  rfl

theorem k9_batch (Z : Pub) (G : Ground) (a : Place) :
    (((k9Ninth Z).batch G a).map fun mk => skel (mk fun s => .ok ([], s))) =
      k9BatchSk (k9Stretches Z) a := by
  rw [k9_batch_is]
  unfold k9BatchSk
  split
  · cases ((k9Ws (k9Stretches Z)).lookup _).bind id with
    | none => rfl
    | some p =>
      show (if p.piece == a.piece then some fun g => K9.batch atS p g else none).map _ =
        if p.piece == a.piece then some (batchSk p) else none
      split <;> rfl
  · rfl

theorem k9_each (Z : Pub) (G : Ground) (l : Nat) :
    ((k9Ninth Z).each G l).isSome = (K9.testsWhere Z.p.X l 0).isSome := by
  show ((K9.testsWhere Z.p.X l 0).map _).isSome = _
  rw [Option.isSome_map]

theorem k9_tests (Z : Pub) (G : Ground) (l : Nat) :
    ((k9Ninth Z).tests G l).isSome = (K9.testsWhere Z.p.X l 0).isSome := by
  show ((K9.testsWhere Z.p.X l 0).map _).isSome = _
  rw [Option.isSome_map]

/-- **The lot's skeleton, as a function of what the lot reads.** tw: whether the segment's sort and
numbers can be read off the public parameters. -/
def k9Sk (groups : Array OnBytes.ReqGroup) (xs : List (Spot × List Fmt.DeclaredRound × Nat))
    (tw : Nat → Bool) : LotSk :=
  { name := "K9: the batching at the gatherer; each; tests; the closing as three blocks"
    letters := false, still := [], blocks := k9BlocksSk groups xs, batch := k9BatchSk xs
    each := tw, tests := tw }

/-- **THE ROW, AT EVERY Z AND G.** -/
theorem k9_row (Z : Pub) (G : Ground) :
    lotSk G (k9Ninth Z) = k9Sk Z.s₀.check.frame.groups (k9Stretches Z)
      (fun l => (K9.testsWhere Z.p.X l 0).isSome) := by
  have e2 : (fun a => ((k9Ninth Z).batch G a).map fun mk => skel (mk fun s => .ok ([], s))) =
      k9BatchSk (k9Stretches Z) := funext (k9_batch Z G)
  have e3 : (fun l => ((k9Ninth Z).each G l).isSome) =
      fun l => (K9.testsWhere Z.p.X l 0).isSome := funext (k9_each Z G)
  have e4 : (fun l => ((k9Ninth Z).tests G l).isSome) =
      fun l => (K9.testsWhere Z.p.X l 0).isSome := funext (k9_tests Z G)
  unfold lotSk k9Sk
  rw [k9_blocks, e2, e3, e4]
  rfl

end Johnson.AtFull.Desc.Lots

#print axioms Johnson.AtFull.Desc.Lots.told_empty
#print axioms Johnson.AtFull.Desc.Lots.skel_batch
#print axioms Johnson.AtFull.Desc.Lots.skel_closeOf
#print axioms Johnson.AtFull.Desc.Lots.skel_refuser
#print axioms Johnson.AtFull.Desc.Lots.k10Par_eq
#print axioms Johnson.AtFull.Desc.Lots.k9CloseAt_skel
#print axioms Johnson.AtFull.Desc.Lots.k9_own
#print axioms Johnson.AtFull.Desc.Lots.k9_blocks
#print axioms Johnson.AtFull.Desc.Lots.k9_batch_is
#print axioms Johnson.AtFull.Desc.Lots.k9_batch_form
#print axioms Johnson.AtFull.Desc.Lots.k9_steady
#print axioms Johnson.AtFull.Desc.Lots.k9_batch
#print axioms Johnson.AtFull.Desc.Lots.k9_each
#print axioms Johnson.AtFull.Desc.Lots.k9_tests
#print axioms Johnson.AtFull.Desc.Lots.k9_row
