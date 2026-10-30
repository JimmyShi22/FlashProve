-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/TableW.lean: A LIGHT FILE: IT IMPORTS Johnson/IMR/WrittenList.lean AND Johnson/IMR/HandsDef.lean ALONE, NONE OF THIS FOLDER's FILES ON THE SEATS; link_numbers | number_at · hear_numbers | hear_number_at · back_numbersW · no_rows_355. OVER ANOTHER SET OF THIS PROJECT's LEAN FILES: e₁ AT THE PROOF FILE: THE CLOSED FACTS ON THE WRITTEN LIST OF PLACES: what the table of joints (Johnson/Desc/First/Borders.lean) says at placesW (Johnson/IMR/WrittenList.lean: the driver's written list at the goals' 25 links), AS BOOLS, WITH THE KERNEL's YES, A COUNT
THAT SHOWS THAT THEY ASK SOMETHING, AND A NEGATIVE TEST (a control) THAT FAILS AS IT MUST.
OBJECT. standAt · mayWait · the place's link at two neighbouring places; quietRow (rowOf linksW p). USER. Whoever carries shapeAt | rowsHeld | membersHeld past a block that keeps the stand (shape_step, Johnson/Desc/First/Link/Law/RbDef.lean; hands_quiet, Johnson/IMR/HandsDef.lean): this folder's own line of the ledger (K3 · K4 · K5 · K6 · K8 · K11), K1's later sendings, the frames' blocks.
BESIDE IT: Johnson/Desc/First/Link/Law/LinkPlacesFit.lean (linkFit, at its 100 numbers: the batching · behind it · the one equation · the shutting): this file covers the three at ALL 357 neighbours and «the row is quiet» at ALL 358; what that file's four lines ask beside stays that file's.

  sameBorder links p p'   the stand, the link and mayWait are the same at the two places.
  pairsOf placesW   placesW with its own tail: 357 pairs.
  same_count        sameBorder holds at 253 of the 357 pairs. (The other 104: the stand turns at 53 blocks; the link at the front; mayWait at the 25 batchings and the 25 equations.)
  keeper p          the block at p is one of K3 · K4 · K5 · K6 · K8 · K11, or a sending of K1 in a link behind its first place.
  keepers_same      at every pair whose first place is a keeper's: sameBorder. keepers_count: there are 151 such pairs.
  quietKind · quiet_kinds   every place of the kinds frame · K3 · K4 · K5 · K6 · K7 · K8 · K11 · K13 has a quiet row: quiet_count: 180 places; quiet_rows: 230 of the 358 rows are quiet.
  bent · bent_fails   THE CONTROL: with the places number 9 and 10 (link 0's batching and the block behind it) changed over keepers_same's Bool is false.
  bentUnseen · bent_unseen   WHAT THE TEST DOES NOT SEE (a first control, which did not fail): two keepers of one link changed over (the places number 3 and 4): the three are the same at both: the Bool stays true.
  same_at · quiet_at   the two Bools, drawn at a number k.
  link_numbers · number_at   THE NUMBERS AGAINST THE PLACES: for l < 25 and j < nAt l + 7 the place number 14 l + 1 + j stands in chain 1, in link l, at piece j.
  hear_numbers · hear_number_at   in front of a link's batching the place number 14 l + i + 2 IS the driver's address (1, some l, i + 1, k), k the kind number i of the link's sort.
  back_numbersW     the places number 0 and 353 … 357 stand in no link, at the pieces 0 and 1 … 5.
  no_rows_355       no class of rows is open at the border number 355: rowSegs (openAt linksW placesW 355) = [].

What is not claimed. That placesW is a description's list: Johnson/IMR/PlacesScope.lean's
places_scope, in scope. Nothing on a state. No soundness.
-/
import Johnson.IMR.WrittenList
import Johnson.IMR.HandsDef

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (ModelPart standAt mayWait rowOf quietRow rowSegs kindsBeforeBatching)

/-- The stand, the link and «a count of rows may wait» are the same at the two places. -/
def sameBorder (links : List ModelPart) (p p' : Place) : Bool :=
  standAt links p == standAt links p' && p.link == p'.link && mayWait links p == mayWait links p'

/-- A list of places with its own tail. -/
def pairsOf (ps : List Place) : List (Place × Place) := ps.zip (ps.drop 1)

/-- The block at p keeps the stand: by its kind. -/
def keeper (p : Place) : Bool :=
  p.kind == .K3 || p.kind == .K4 || p.kind == .K5 || p.kind == .K6 || p.kind == .K8 ||
    p.kind == .K11 || (p.kind == .K1 && p.link.isSome && p.piece != 1)

def keepersFit (links : List ModelPart) (ps : List Place) : Bool :=
  (pairsOf ps).all fun x => !keeper x.1 || sameBorder links x.1 x.2

def quietKind (k : KindName) : Bool :=
  k == .frame || k == .K3 || k == .K4 || k == .K5 || k == .K6 || k == .K7 || k == .K8 ||
    k == .K11 || k == .K13

def quietFit (links : List ModelPart) (ps : List Place) : Bool :=
  ps.all fun p => !quietKind p.kind || quietRow (rowOf links p)

set_option maxRecDepth 1000000 in
theorem same_count : ((pairsOf placesW).countP fun x => sameBorder linksW x.1 x.2) = 253 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem keepers_same : keepersFit linksW placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem keepers_count : ((pairsOf placesW).countP fun x => keeper x.1) = 151 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem quiet_kinds : quietFit linksW placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem quiet_count : (placesW.countP fun p => quietKind p.kind) = 180 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem quiet_rows : (placesW.countP fun p => quietRow (rowOf linksW p)) = 230 := by decide +kernel

/-- THE CONTROL: the places number 9 and 10 (link 0's batching and the block behind it) changed over. -/
def bent : List Place :=
  placesW.take 9 ++ (placesW.drop 10).take 1 ++ (placesW.drop 9).take 1 ++ placesW.drop 11

/-- What the test does NOT see: two keepers of one link changed over (the places number 3 and 4). -/
def bentUnseen : List Place :=
  placesW.take 3 ++ (placesW.drop 4).take 1 ++ (placesW.drop 3).take 1 ++ placesW.drop 5

set_option maxRecDepth 1000000 in
theorem bent_fails : keepersFit linksW bent = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem bent_unseen : keepersFit linksW bentUnseen = true := by decide +kernel

/-- keepers_same, drawn at a number. -/
theorem same_at {k : Nat} {p p' : Place} (h : placesW[k]? = some p) (h' : placesW[k + 1]? = some p')
    (hk : keeper p = true) :
    standAt linksW p' = standAt linksW p ∧ p'.link = p.link ∧
      mayWait linksW p' = mayWait linksW p := by
  have hm : (p, p') ∈ pairsOf placesW := by
    unfold pairsOf
    refine List.mem_of_getElem? (i := k) ?_
    rw [List.getElem?_zip_eq_some]
    refine ⟨h, ?_⟩
    rw [List.getElem?_drop, Nat.add_comm]
    exact h'
  have h1 := List.all_eq_true.1 keepers_same _ hm
  rw [hk] at h1
  have h2 : sameBorder linksW p p' = true := by simpa using h1
  unfold sameBorder at h2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨h2.1.1.symm, h2.1.2.symm, h2.2.symm⟩

/-- quiet_kinds, drawn at a number. -/
theorem quiet_at {k : Nat} {p : Place} (h : placesW[k]? = some p) (hk : quietKind p.kind = true) :
    quietRow (rowOf linksW p) = true := by
  have h1 := List.all_eq_true.1 quiet_kinds _ (List.mem_of_getElem? h)
  rw [hk] at h1
  simpa using h1

/-- The numbers against the places, in the links: a Bool. -/
def numbersFit (ps : List Place) : Bool :=
  (List.range 25).all fun l => (List.range (nAt l + 7)).all fun j =>
    (ps[14 * l + 1 + j]?).any fun p => p.chain == 1 && p.link == some l && p.piece == j

set_option maxRecDepth 1000000 in
theorem link_numbers : numbersFit placesW = true := by decide +kernel

/-- link_numbers, drawn at a link and a piece. -/
theorem number_at {l j : Nat} (hl : l < 25) (hj : j < nAt l + 7) :
    ∃ p, placesW[14 * l + 1 + j]? = some p ∧ p.chain = 1 ∧ p.link = some l ∧ p.piece = j := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 link_numbers l (List.mem_range.2 hl)) j
    (List.mem_range.2 hj)
  cases hp : placesW[14 * l + 1 + j]? with
  | none => rw [hp] at h1; cases h1
  | some p =>
    rw [hp] at h1
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h1
    exact ⟨p, rfl, h1.1.1, h1.1.2, h1.2⟩

/-- In front of a link's batching: the place number 14 l + i + 2 is the driver's address (1, some l, i + 1, ‹the kind number i of the link's sort›): a Bool. -/
def hearFit (ps : List Place) : Bool :=
  (List.range 25).all fun l => (List.range (nAt l)).all fun i =>
    match (kindsBeforeBatching (subW l) (l == 0))[i]? with
    | some k => ps[14 * l + i + 2]? == some { chain := 1, link := some l, piece := i + 1, kind := k }
    | none => false

set_option maxRecDepth 1000000 in
theorem hear_numbers : hearFit placesW = true := by decide +kernel

/-- hear_numbers, drawn at a link and a number. -/
theorem hear_number_at {l i : Nat} {k : KindName} (hl : l < 25)
    (hk : (kindsBeforeBatching (subW l) (l == 0))[i]? = some k) (hi : i < nAt l) :
    placesW[14 * l + i + 2]? = some { chain := 1, link := some l, piece := i + 1, kind := k } := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 hear_numbers l (List.mem_range.2 hl)) i
    (List.mem_range.2 hi)
  rw [hk] at h1
  exact beq_iff_eq.1 h1

set_option maxRecDepth 1000000 in
theorem back_numbersW :
    (placesW[0]?).map (fun p => (p.link, p.piece)) = some (none, 0) ∧
      ∀ j < 5, (placesW[353 + j]?).map (fun p => (p.link, p.piece)) = some (none, j + 1) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem no_rows_355 : rowSegs (openAt linksW placesW 355) = [] := by decide +kernel

end IM

#print axioms IM.link_numbers
#print axioms IM.number_at
#print axioms IM.hear_numbers
#print axioms IM.hear_number_at
#print axioms IM.back_numbersW
#print axioms IM.no_rows_355
#print axioms IM.same_count
#print axioms IM.keepers_same
#print axioms IM.keepers_count
#print axioms IM.quiet_kinds
#print axioms IM.quiet_count
#print axioms IM.quiet_rows
#print axioms IM.bent_fails
#print axioms IM.bent_unseen
#print axioms IM.same_at
#print axioms IM.quiet_at
