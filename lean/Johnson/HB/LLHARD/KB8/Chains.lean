-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/Chains.lean: the declared rounds of a key file's description
(`Key.descriptionFromSource`, Johnson/Desc/Key/Desc.lean), as plain appends of the parts that have rounds, general
in what the description is made of. Definitions, statements and proofs; nothing is evaluated.

Main names.
  `sendRounds`, `lookRounds`, `battRoundsOf`: the rounds of a sending, of a lookup's block, of the
    batching of the rows on the table, each from just what it reads.
  `firstRoundsOf`, `sharedRoundsOf`: the first and the shared chain's rounds.
  `first_rounds`, `shared_rounds`, `third_rounds`: the three chains' flat lists have these rounds.
  `decl_eq`: **the description's declared rounds**, at all X, N, P.

What falls out. Of X the right side names X.set, four fields of X.Y.k.oneTime (ranges, lin,
indexMasks, codes) and X.chains.made.sized.key. The declared rounds and the tenants that X holds
(X.Y.D, X.Y.told) are not named: the first chain hands them to its blocks' oracle messages and
lists "fixed before the draw" alone.

Limits. The four proximity tests' rounds stand on the right side as their blocks' rounds: what these
are is `k12_rounds_at` (Laws.lean in this folder). Nothing on any value. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params

/-! ## The parts -/

/-- A sending's two rounds, from the codes, the bits of work and the messages. -/
def sendRounds (codes : Codes) (work : Nat) (msg : Array OracleNotice) : List Fmt.DeclaredRound :=
  K1.rounds { place := ⟨0, none, 0, .K1⟩, codes := codes, gp := { samples := 0, firstTree := 0 }
              work := work, parts := [("", msg)] }

/-- The rounds of a lookup's block on a key file's first chain. -/
def lookRounds (set : Setting) (x : Lookup) : List Fmt.DeclaredRound :=
  ((K3.entriesG set .once (K3.faceOfLkp x)).getD []).map fun e => { entry := e }

/-- The rounds of the batching of the rows on the table. -/
def battRoundsOf (ranges : WfPublic) (lin : LinShape) : List Fmt.DeclaredRound :=
  K13.battRounds { chain := 1, piece := 0, pieceRows := 0
                   rows := sumT (ranges.lookups.map (·.parts.length)), reply := false, lin := lin
                   sent := 0 }

/-- **The first chain's rounds.** look: a lookup's rounds; rng: the ranges' test's. -/
def firstRoundsOf (look : Lookup → List Fmt.DeclaredRound) (ranges : WfPublic) (lin : LinShape)
    (idx : OracleNotice) (codes : Codes) (rng : List Fmt.DeclaredRound) : List Fmt.DeclaredRound :=
  sendRounds codes 0 #[idx] ++ (sendRounds codes 0 (Wf.messageOf ranges) ++
    ((Wf.lookupsOf ranges (Wf.matrixOf lin)).flatMap look ++ (rng ++ (battRoundsOf ranges lin ++
      (((linMessageW lin).map (sendRounds codes 0)).getD [] ++ [ChainEnd.sealRound])))))

/-- `Key.sharedPar`'s text at the sized key. -/
def par14 (z : Plan.KeySized) (beforePoint : List (Nat × Nat)) : _root_.Desc.K14.P14 :=
  { set := z.set, scope := if z.once.lines.oneTime then .once else .shared, codes := z.codes,
    S := z.once.shape, item := 0, beforePoint := beforePoint }

/-- **The shared chain's rounds.** u, o: the two proximity tests'. -/
def sharedRoundsOf (z : Plan.KeySized) (u o : List Fmt.DeclaredRound) : List Fmt.DeclaredRound :=
  (_root_.Desc.K14.blocksOr (par14 z [])).flatMap (·.rounds) ++ (u ++ (o ++ [ChainEnd.sealRound]))

/-! ## The first chain -/

/-- Of a lookup's link the lookup's own block alone has rounds. -/
theorem look_rounds (one : OneTime) (set : Setting) (i : Nat) (x : Lookup) :
    (lookupLink one set i x).blocksInOrder.flatMap (·.rounds) = lookRounds set x := by
  have c1 : (caller one i x).rounds = [] := rfl
  have c2 : (K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x) :
      Block FirstState Claim).rounds = lookRounds set x := rfl
  have c3 : ∀ cl, (layer one set i x cl).rounds = [] := fun _ => rfl
  rw [link_rounds]
  simp only [lookupLink, List.flatMap_cons, List.flatMap_nil, c1, c2, c3, List.nil_append,
    List.append_nil]

/-- Of the four blocks at the batching's place the batching alone has rounds. -/
theorem batch_rounds (one : OneTime) (s : Nat) :
    (batchTableRows (·.keys) one pieces s : Block FirstState Claim).rounds =
      battRoundsOf one.ranges one.lin := by
  show (([] ++ []) ++ K13.battRounds (batchWhere one pieces s)) ++ [] = _
  rw [List.append_nil]
  rfl

/-- W's sending, where the shape has one: a sending's two rounds. -/
theorem sendW_rounds (one : OneTime) (s : Nat) (g : List (List Nat)) :
    (sendW one pieces s g : Option (Block FirstState Claim)).toList.flatMap (·.rounds) =
      ((linMessageW one.lin).map (sendRounds one.codes 0)).getD [] := by
  unfold sendW
  cases linMessageW one.lin with
  | none => rfl
  | some msg => rfl

/-- **The first chain's flat list has these rounds.** -/
theorem first_rounds (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root)
    (set : Setting) (N : H2U.PlaceNums) :
    (firstChain one D told set N).blocksInOrder.flatMap (·.rounds) =
      firstRoundsOf (lookRounds set) one.ranges one.lin one.indexMasks one.codes
        (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Claim).rounds := by
  have h1 : ∀ g, (sendIndexMasks one pieces g : Block FirstState Claim).rounds =
      sendRounds one.codes 0 #[one.indexMasks] := fun _ => rfl
  have h2 : ∀ g, (sendOwnMessage one pieces g : Block FirstState Claim).rounds =
      sendRounds one.codes 0 (Wf.messageOf one.ranges) := fun _ => rfl
  have h4 : (layRows one).rounds = [] := rfl
  have h5 : (rangesTest (enterRanges one) leaveRanges N : Block FirstState Claim).rounds =
      (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Claim).rounds := rfl
  have h8 : ∀ l, (firstChainEnd pieces l : Block FirstState Claim).rounds =
      [ChainEnd.sealRound] := fun _ => rfl
  rw [flat_rounds]
  simp only [firstChain, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, flatMap_map',
    look_rounds, zipIdx_flatMap, h1, h2, h4, h5, h8, batch_rounds, sendW_rounds, List.nil_append,
    List.append_nil, List.append_assoc, firstRoundsOf, lookupsOf]

/-! ## The shared chain -/

/-- What must be fixed before the shared point goes into no round. -/
theorem blocksOr_rounds (z : Plan.KeySized) (b : List (Nat × Nat)) :
    (_root_.Desc.K14.blocksOr (par14 z b)).flatMap (·.rounds) =
      (_root_.Desc.K14.blocksOr (par14 z [])).flatMap (·.rounds) := by
  unfold _root_.Desc.K14.blocksOr _root_.Desc.K14.blocks
  show List.flatMap _ (Option.getD (Option.bind (_root_.Desc.K14.withU z.once.shape) _) _) =
    List.flatMap _ (Option.getD (Option.bind (_root_.Desc.K14.withU z.once.shape) _) _)
  cases _root_.Desc.K14.withU z.once.shape <;> rfl

/-- **The shared chain's flat list has these rounds.** -/
theorem shared_rounds (c : Model.Verify.Chains) (P : LaterPlaces) :
    ((sharedChain c P).retype : Chain _root_.Desc.K14.St Claim).blocksInOrder.flatMap (·.rounds) =
      sharedRoundsOf c.made.sized.key
        (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block K12.T12 Unit).rounds
        (P.O.toList.flatMap fun nO =>
          (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) :
            Block K12.T12 Unit).rounds) := by
  have h0 : (sharedFront c).rounds = [] := rfl
  have h9 : ∀ l, (K12.Seat.last l).rounds = [ChainEnd.sealRound] := fun _ => rfl
  have hb : (_root_.Desc.K14.blocksOr (sharedPar c (beforeSharedPoint P))).flatMap (·.rounds) =
      (_root_.Desc.K14.blocksOr (par14 c.made.sized.key [])).flatMap (·.rounds) :=
    blocksOr_rounds c.made.sized.key (beforeSharedPoint P)
  have hu : ∀ b : Block K12.T12 Unit, (K12.Seat.onGu b).rounds = b.rounds := fun _ => rfl
  have ho : ∀ b : Block K12.T12 Unit, (K12.Seat.onGomega b).rounds = b.rounds := fun _ => rfl
  rw [retype_rounds _ rfl, flat_rounds]
  simp only [sharedChain, sharedTests, List.flatMap_cons, List.flatMap_append, List.flatMap_nil,
    flatMap_map', h0, h9, hb, hu, ho, List.nil_append, List.append_nil, List.append_assoc,
    sharedRoundsOf]

/-! ## The third chain -/

/-- **The third chain's flat list has the own test's rounds.** -/
theorem third_rounds (c : Model.Verify.Chains) (P : LaterPlaces) :
    ((thirdChain c P).retype : Chain Third.S₃ Claim).blocksInOrder.flatMap (·.rounds) =
      (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block K12.T12 Unit).rounds := by
  rw [retype_rounds _ rfl, flat_rounds]
  show [] ++ ([] ++ ([] ++ (([] ++ ((K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) :
    Block K12.T12 Unit).rounds ++ [])) ++ []))) = _
  simp only [List.nil_append, List.append_nil]

/-! ## The description -/

/-- **The declared rounds of a key file's description.** -/
theorem decl_eq (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) :
    (descriptionFromSource X N P).roundsDeclaredByBlocks =
      (firstRoundsOf (lookRounds X.set) X.Y.k.oneTime.ranges X.Y.k.oneTime.lin
          X.Y.k.oneTime.indexMasks X.Y.k.oneTime.codes
          (K12.proximityTestKind K12.guardedProximityTestParts (rangesParams N) : Block K12.T12 Claim).rounds,
        sharedRoundsOf X.chains.made.sized.key
          (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block K12.T12 Unit).rounds
          (P.O.toList.flatMap fun nO =>
            (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) :
              Block K12.T12 Unit).rounds),
        (K12.proximityTestKind K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block K12.T12 Unit).rounds) :=
  Prod.ext (first_rounds X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N)
    (Prod.ext (shared_rounds X.chains P) (third_rounds X.chains P))

end Johnson.KB8

#print axioms Johnson.KB8.look_rounds
#print axioms Johnson.KB8.batch_rounds
#print axioms Johnson.KB8.sendW_rounds
#print axioms Johnson.KB8.first_rounds
#print axioms Johnson.KB8.blocksOr_rounds
#print axioms Johnson.KB8.shared_rounds
#print axioms Johnson.KB8.third_rounds
#print axioms Johnson.KB8.decl_eq
