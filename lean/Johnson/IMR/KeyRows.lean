-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyRows.lean: THE ROWS OF A KEY FILE's DESCRIPTION: for each of its three
chains the places and the NUMBERS OF ROUNDS of all its sub-protocols, in order, GENERAL IN X N P: no
premise, no evaluation. For the row r5
(wantedOk) of KeyBackOfRows.lean. It stands over the files Johnson/HB/LLHARD/KB8/ (Laws ·
Chains: what the sub-protocols' ROUNDS are), and is their pattern once more, with «place and number
of rounds» in the place of «rounds».

WHAT IS SAID.
  rowOf b          a sub-protocol's row: its place and its number of rounds.
  rowsOf_map       rowsOf (Johnson/RunOne/Sound/KeyListsAtFK.lean) is the list of rows.
  flat_rows · link_rows · retype_rows   the rows of a chain's flat list, of a link's, of a chain
                   carried to another type of claims.
  test_row         the proximity test's sub-protocol stands at the place that it was handed,
                   whatever its numbers: by p12At_place · k12_place
                   (Johnson/Desc/K14/Law/SharedKinds.lean): CALLED, NOT TYPED AGAIN.
  look_rows        a lookup's link has the table's own six rows (wantedLink), at the number of
                   rounds of its one sub-protocol with rounds.
  firstRowsOf, first_rows · sharedRowsOf, shared_rows · third_rows   **the three chains' rows.**
SO WHAT THE ROWS READ OF X N P IS LEAN's WORD: of the one-time chain's values: ranges · lin ·
indexMasks · codes; X.set; the sized key; and of each proximity test's place its sub-protocol's
number of rounds. The declared rounds as handed in (D), the tenants as told, the parameter bytes,
the digest: NOT ON THE RIGHT SIDES.
What is not claimed. Any number. That the rows are the table's: IMR/KeyRowsFull.lean. No soundness.

-/
import Johnson.HB.LLHARD.KB8.Row
import Johnson.RunOne.Sound.KeyPlacesInScope
import Johnson.Desc.K14.Law.SharedKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open Johnson.KB8
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Sound (rowsOf)
open _root_.Desc.K14.Law (p12At_place k12_place)

variable {S Cl Cl' : Type}

/-- A sub-protocol's row of the table of places: its place and its number of rounds. -/
def rowOf (b : Block S Cl) : Place × Nat := (b.place, b.rounds.length)

/-! ## General laws -/

/-- rowsOf (Johnson/RunOne/Sound/KeyListsAtFK.lean) is the list of these rows. -/
theorem rowsOf_map (bs : List (Block S Cl)) : rowsOf bs = bs.map rowOf := rfl

theorem flat_rows (c : Chain S Cl) :
    c.blocksInOrder.map rowOf = rowOf c.first :: (c.front.map rowOf ++
               (c.links.flatMap (fun L => L.blocksInOrder.map rowOf) ++ (c.back.map rowOf ++ [rowOf c.last]))) := by
  unfold Chain.blocksInOrder
  simp only [List.map_cons, List.map_append, List.map_map, List.map_flatMap, List.map_nil,
    List.cons_append, List.append_assoc]
  rfl

theorem link_rows (L : Link S Cl) :
    L.blocksInOrder.map rowOf = (⟨L.chain, some L.number, 0, .frame⟩, 0) :: (L.hear.map rowOf ++
               (rowOf (L.batch (claimsInBy L.each L.hear L.order)) ::
                 (⟨L.chain, some L.number, L.hear.length + 2, .frame⟩, 0) :: (L.close.map rowOf ++
                   [(⟨L.chain, some L.number, L.hear.length + L.close.length + 3, .frame⟩, 0)]))) := by
  unfold Link.blocksInOrder
  simp only [List.map_cons, List.map_append, List.map_nil, List.cons_append, List.append_assoc,
    List.nil_append]
  rfl

theorem retype_rows (c : Chain S Cl) (h : c.links = []) :
    (c.retype : Chain S Cl').blocksInOrder.map rowOf = c.blocksInOrder.map rowOf := by
  rw [flat_rows, flat_rows, h]
  simp only [Chain.retype, List.map_map, List.flatMap_nil]
  rfl

/-! ## The first chain -/

theorem look_rows (one : OneTime) (set : Setting) (i : Nat) (x : Lookup) :
    (lookupLink one set i x).blocksInOrder.map rowOf = wantedLink i (lookRounds set x).length := by
  rw [link_rows]
  rfl

/-- The first chain's rows. look: a lookup's number of rounds; rng: the ranges' test's. -/
def firstRowsOf (look : Lookup → Nat) (ranges : WfPublic) (lin : LinShape) (idx : OracleNotice)
    (codes : Codes) (rng : Nat) : List (Place × Nat) :=
  (⟨1, none, 1, .K1⟩, (sendRounds codes 0 #[idx]).length) ::
    ((⟨1, none, 2, .K1⟩, (sendRounds codes 0 (Wf.messageOf ranges)).length) ::
      (((Wf.lookupsOf ranges (Wf.matrixOf lin)).zipIdx.flatMap fun x =>
          wantedLink x.2 (look x.1)) ++
        ((⟨1, none, 4, .frame⟩, 0) :: (⟨1, none, 5, .K12⟩, rng) ::
          (⟨1, none, 13, .K13⟩, (battRoundsOf ranges lin).length) ::
          (((linMessageW lin).map fun msg =>
              ((⟨1, none, 14, .K1⟩ : Place), (sendRounds codes 0 msg).length)).toList ++
            [(⟨1, none, 15, .frame⟩, 1)]))))

theorem sendW_rows (one : OneTime) (s : Nat) (g : List (List Nat)) :
    (sendW one pieces s g : Option (Block FirstState Key.Claim)).toList.map rowOf =
      ((linMessageW one.lin).map fun msg =>
        ((⟨1, none, 14, .K1⟩ : Place), (sendRounds one.codes 0 msg).length)).toList := by
  unfold sendW
  cases linMessageW one.lin with
  | none => rfl
  | some msg => rfl

theorem first_rows (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) :
    (firstChain one D told set N).blocksInOrder.map rowOf =
      firstRowsOf (fun x => (lookRounds set x).length) one.ranges one.lin one.indexMasks one.codes
        (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Key.Claim).rounds.length := by
  have h1 : ∀ g, rowOf (sendIndexMasks one pieces g : Block FirstState Key.Claim) =
      (⟨1, none, 1, .K1⟩, (sendRounds one.codes 0 #[one.indexMasks]).length) := fun _ => rfl
  have h2 : ∀ g, rowOf (sendOwnMessage one pieces g : Block FirstState Key.Claim) =
      (⟨1, none, 2, .K1⟩, (sendRounds one.codes 0 (Wf.messageOf one.ranges)).length) :=
    fun _ => rfl
  have h4 : rowOf (layRows one) = (⟨1, none, 4, .frame⟩, 0) := rfl
  have h5 : rowOf (rangesTest (enterRanges one) leaveRanges N : Block FirstState Key.Claim) =
      (⟨1, none, 5, .K12⟩,
        (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Key.Claim).rounds.length) := by
    have e : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Key.Claim).place =
        (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Key.Claim).place := rfl
    unfold rowOf
    rw [e, k12_place]
    unfold rangesParams
    rw [p12At_place]
    rfl
  have h6 : ∀ s, rowOf (batchTableRows (·.keys) one pieces s : Block FirstState Key.Claim) =
      (⟨1, none, 13, .K13⟩, (battRoundsOf one.ranges one.lin).length) := fun s => by
    unfold rowOf
    rw [batch_rounds]
    rfl
  have h8 : ∀ l, rowOf (firstChainEnd pieces l : Block FirstState Key.Claim) =
      (⟨1, none, 15, .frame⟩, 1) := fun _ => rfl
  rw [flat_rows]
  simp only [firstChain, List.map_cons, List.map_nil, flatMap_map', look_rows, h1, h2, h4, h5, h6,
    h8, sendW_rows, List.nil_append, List.cons_append, firstRowsOf, lookupsOf]

/-! ## The shared chain -/

/-- What must be fixed before the shared point goes into no row. -/
theorem blocksOr_rows (z : Plan.KeySized) (b : List (Nat × Nat)) :
    (_root_.Desc.K14.blocksOr (par14 z b)).map rowOf =
      (_root_.Desc.K14.blocksOr (par14 z [])).map rowOf := by
  unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks
  show List.map _ (Option.getD (Option.bind (_root_.Desc.K14.withU z.once.shape) _) _) =
    List.map _ (Option.getD (Option.bind (_root_.Desc.K14.withU z.once.shape) _) _)
  cases _root_.Desc.K14.withU z.once.shape <;> rfl

/-- The shared chain's rows. u: the folded row's test's number of rounds; o: Omega's, if any. -/
def sharedRowsOf (z : Plan.KeySized) (u : Nat) (o : List Nat) : List (Place × Nat) :=
  (⟨2, none, 0, .frame⟩, 0) :: ((_root_.Desc.K14.blocksOr (par14 z [])).map rowOf ++
    ((⟨2, none, 9, .K12⟩, u) :: (o.map (fun n => ((⟨2, none, 10, .K12⟩ : Place), n)) ++
      [(⟨2, none, 11, .frame⟩, 1)])))

theorem test_row {T : Type} (X : K12.Parts T) (place : Place) (x : H2U.PlaceNums) :
    rowOf (K12.proximityTestKind X (H2U.proximityTestParametersAt place x) : Block T Cl) =
      (place, (K12.proximityTestKind X (H2U.proximityTestParametersAt place x) : Block T Cl).rounds.length) := by
  unfold rowOf
  rw [k12_place, p12At_place]

theorem shared_rows (c : Model.Verify.Chains) (P : LaterPlaces) :
    ((sharedChain c P).retype : Chain _root_.Desc.K14.St Key.Claim).blocksInOrder.map rowOf =
      sharedRowsOf c.made.sized.key
        (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) :
          Block K12.T12 Unit).rounds.length
        (P.O.toList.map fun nO =>
          (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) :
            Block K12.T12 Unit).rounds.length) := by
  have h0 : rowOf (sharedFront c) = (⟨2, none, 0, .frame⟩, 0) := rfl
  have h9 : ∀ l, rowOf (K12.Seat.last l) = (⟨2, none, 11, .frame⟩, 1) := fun _ => rfl
  have hb : (_root_.Desc.K14.blocksOr (sharedPar c (beforeSharedPoint P))).map rowOf =
      (_root_.Desc.K14.blocksOr (par14 c.made.sized.key [])).map rowOf :=
    blocksOr_rows c.made.sized.key (beforeSharedPoint P)
  have hu : ∀ b : Block K12.T12 Unit, rowOf (K12.Seat.onGu b) = rowOf b := fun _ => rfl
  have ho : ∀ b : Block K12.T12 Unit, rowOf (K12.Seat.onGomega b) = rowOf b := fun _ => rfl
  rw [retype_rows _ rfl, flat_rows]
  simp only [sharedChain, sharedTests, List.map_cons, List.map_append, List.map_nil, List.map_map,
    List.flatMap_nil, Function.comp_def, h0, h9, hb, hu, ho, test_row, List.nil_append,
    List.cons_append, List.append_assoc, sharedRowsOf]

/-! ## The third chain -/

theorem third_rows (c : Model.Verify.Chains) (P : LaterPlaces) :
    ((thirdChain c P).retype : Chain Third.S₃ Key.Claim).blocksInOrder.map rowOf =
      [(⟨3, none, 0, .K14⟩, 0), (⟨3, none, 1, .frame⟩, 0),
        (⟨3, none, 2, .K12⟩, (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
          Block K12.T12 Unit).rounds.length), (⟨3, none, 3, .frame⟩, 0)] := by
  have hp : (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
      Block K12.T12 Unit).place = ⟨3, none, 2, .K12⟩ := by rw [k12_place, p12At_place]
  have hw : rowOf (Third.ownAt (ownTest P)) = (⟨3, none, 2, .K12⟩,
      (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
        Block K12.T12 Unit).rounds.length) := by
    show (({ (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
      Block K12.T12 Unit).place with chain := 3, link := none, piece := 2 } : Place), _) = _
    rw [hp]
    rfl
  rw [retype_rows _ rfl, flat_rows]
  show _ :: ([] ++ ([] ++ ([_, rowOf (Third.ownAt (ownTest P))] ++ [_]))) = _
  rw [hw]
  rfl

end IM

#print axioms IM.rowsOf_map
#print axioms IM.flat_rows
#print axioms IM.link_rows
#print axioms IM.retype_rows
#print axioms IM.look_rows
#print axioms IM.sendW_rows
#print axioms IM.first_rows
#print axioms IM.blocksOr_rows
#print axioms IM.test_row
#print axioms IM.shared_rows
#print axioms IM.third_rows
