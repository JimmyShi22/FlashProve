-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyCut23.lean (the last chain's end is pinned as a term, not by its name · the chains' numbers of blocks stand as propositions). WHICH BLOCKS STAND IN THE KEY FILE's SHARED AND LAST CHAIN, AS EQUATIONS OF LISTS: for whoever instances a kind's law at a place of the key file.
  seat b            a kind's block (no claims' type) as the key file's description seats it: Block.retype, then what Chain.blocksInOrder does to a block outside a link: name · place · rounds · oracles · before · decide · after ARE b's (seat_…: rfl); claims := []; the test on the plan asks
                    besides that b has no claims and no run behind a batching
  AT THE DESCRIPTION (what descriptionFromPlan m returns):
  shared_flat       PROVED: (descriptionFromSource X N P).shared.blocksInOrder = the front's block :: (K14.blocksOr (p14At X P) ++ sharedTests P ++ [the chain's end]).map seat
  shared_at_blocks  PROVED: so where K14.blocks at THE KEY FILE's OWN P14 := p14At X P gives l: the blocks 1 … 8 of the shared chain are l's, seated, in order
  second_flat       PROVED: the like for the last chain: K14's second part · the taken trees' sources · the own test · the chain's end (end₃At: the term)
  shared_length | second_length   PROVED: twelve blocks (where K14.blocks gives a list and the plan has a test on G_omega) | four
  names_blocks · names₂_at · names₃_at   PROVED: the names are the table's (Johnson/Desc/Key/KeyBorders23.lean: names₂ | names₃), where blocks gives a list and the plan has a test on G_omega
Limits. Equations of lists; no law. Nothing on soundness.

-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.Desc.Key.KeyBorders23

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key

/-- What Chain.blocksInOrder does to a block outside a link. -/
def bareB {σ Cl : Type} (b : Block σ Cl) : Block σ Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- A kind's block as the key file's description seats it. -/
def seat {σ Cl : Type} (b : Block σ Unit) : Block σ Cl := bareB (Block.retype b)

section
variable {σ Cl : Type} (b : Block σ Unit)
theorem seat_name : (seat b : Block σ Cl).name = b.name := rfl
theorem seat_place : (seat b : Block σ Cl).place = b.place := rfl
theorem seat_rounds : (seat b : Block σ Cl).rounds = b.rounds := rfl
theorem seat_oracles : (seat b : Block σ Cl).oracles = b.oracles := rfl
theorem seat_before : (seat b : Block σ Cl).before = b.before := rfl
theorem seat_decide : (seat b : Block σ Cl).decide = b.decide := rfl
theorem seat_after : (seat b : Block σ Cl).after = b.after := rfl
theorem seat_claims : (seat b : Block σ Cl).claims = [] := rfl
end

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- The key file's own parameters of K14. -/
abbrev p14At : _root_.Desc.K14.P14 := sharedPar X.chains (beforeSharedPoint P)

/-- The shared chain's blocks behind the front and in front of the end. -/
def inFront₂ : List (Block _root_.Desc.K14.St Unit) := _root_.Desc.K14.blocksOr (p14At X P) ++ sharedTests P

/-- The front's block as it is seated. -/
def front₂ : Block _root_.Desc.K14.St Claim :=
  bareB { (Block.retype (sharedFront X.chains) : Block _root_.Desc.K14.St Claim) with
    planOk := (Block.retype (sharedFront X.chains) : Block _root_.Desc.K14.St Claim).planOk && true }

theorem shared_flat :
    (descriptionFromSource X N P).shared.blocksInOrder = front₂ X :: (inFront₂ X P ++ [VerifiableInference.Desc.K12.Seat.last (inFront₂ X P)]).map seat := by
  have h : (descriptionFromSource X N P).shared.blocksInOrder =
      front₂ X :: (((inFront₂ X P).map Block.retype).map bareB ++ [seat (VerifiableInference.Desc.K12.Seat.last (inFront₂ X P))]) := rfl
  rw [h, List.map_map, List.map_append]
  rfl

theorem shared_at_blocks (l : List (Block _root_.Desc.K14.St Unit)) (h : _root_.Desc.K14.blocks (p14At X P) = some l) :
    (descriptionFromSource X N P).shared.blocksInOrder =
      front₂ X :: (l.map seat ++ (sharedTests P).map seat ++ [seat (VerifiableInference.Desc.K12.Seat.last (l ++ sharedTests P))]) := by
  have e : inFront₂ X P = l ++ sharedTests P := by
    unfold inFront₂ _root_.Desc.K14.blocksOr
    rw [h]
    rfl
  rw [shared_flat, e, List.map_append, List.map_append]
  rfl

/-- The own test's block, as the last chain holds it. -/
def own₃ : Block VerifiableInference.Desc.Third.S₃ Unit := VerifiableInference.Desc.Third.ownAt (ownTest P)

/-- The last chain's end: the chains' end's one text at the rounds of the three blocks in front. -/
def end₃At : Block VerifiableInference.Desc.Third.S₃ Unit :=
  VerifiableInference.Desc.Third.end₃ [VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (thirdPar X.chains), VerifiableInference.Desc.Third.takenSources (ownTest P), own₃ P]

theorem second_flat : ∃ f : Block VerifiableInference.Desc.Third.S₃ Claim,
    (descriptionFromSource X N P).second.blocksInOrder = [f, seat (VerifiableInference.Desc.Third.takenSources (ownTest P)), seat (own₃ P), seat (end₃At X P)] ∧
      f.name = (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (thirdPar X.chains) : Block VerifiableInference.Desc.Third.S₃ Unit).name ∧
      f.rounds = (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (thirdPar X.chains) : Block VerifiableInference.Desc.Third.S₃ Unit).rounds ∧
      f.decide = (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (thirdPar X.chains) : Block VerifiableInference.Desc.Third.S₃ Unit).decide :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem second_length : (descriptionFromSource X N P).second.blocksInOrder.length = 4 := by
  obtain ⟨f, h, -⟩ := second_flat X N P
  rw [h]
  rfl

end

/-- The eight blocks' names. -/
theorem names_blocks (Q : _root_.Desc.K14.P14) (l : List (Block _root_.Desc.K14.St Unit)) (h : _root_.Desc.K14.blocks Q = some l) :
    l.map (·.name) = ["LIN point", "send o_u", "(rec_gamma)", "LOC", "send o_omega", "joins", "LIN zeta", "SPLIT"] := by
  unfold _root_.Desc.K14.blocks at h
  cases hu : _root_.Desc.K14.withU Q.S with
  | none => simp [hu] at h
  | some u =>
    simp only [hu, bind, Option.bind, pure] at h
    rw [← Option.some.inj h]
    rfl

/-- K12's block bears its place's name, whatever its numbers. -/
theorem k12_name {T Cl : Type} (Y : VerifiableInference.Desc.K12.Parts T) (p : VerifiableInference.Desc.K12.P12) :
    (VerifiableInference.Desc.K12.proximityTestKind Y p : Block T Cl).name = VerifiableInference.Desc.K12.nameAt p.place := by
  unfold VerifiableInference.Desc.K12.proximityTestKind
  split <;> rfl

/-- The place's parameters hold the place. -/
theorem p12At_place (pl : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt pl x).place = pl := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **The shared chain's blocks bear the table's names.** -/
theorem names₂_at (l : List (Block _root_.Desc.K14.St Unit)) (h : _root_.Desc.K14.blocks (p14At X P) = some l) (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (descriptionFromSource X N P).shared.blocksInOrder.map (·.name) = names₂ := by
  rw [shared_at_blocks X N P l h]
  have e8 : (l.map (seat (Cl := Claim))).map (·.name) = l.map (·.name) := by rw [List.map_map]; rfl
  have et : sharedTests P =
      [VerifiableInference.Desc.K12.Seat.onGu (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)),
       VerifiableInference.Desc.K12.Seat.onGomega (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))] := by
    unfold sharedTests
    rw [hO]
    rfl
  have n9 : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block _ Unit).name = "the proximity test (chain 2, piece 9)" := by
    rw [k12_name, p12At_place]
    decide
  have n10 : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block _ Unit).name = "the proximity test (chain 2, piece 10)" := by
    rw [k12_name, p12At_place]
    decide
  have e2 : ((sharedTests P).map (seat (Cl := Claim))).map (·.name) = ["the proximity test (chain 2, piece 9)", "the proximity test (chain 2, piece 10)"] := by
    rw [et]
    show [(VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block _ Unit).name,
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block _ Unit).name] = _
    rw [n9, n10]
  have key : ((front₂ X :: (l.map seat ++ (sharedTests P).map seat ++ [seat (VerifiableInference.Desc.K12.Seat.last (l ++ sharedTests P))]) :
      List (Block _root_.Desc.K14.St Claim))).map (·.name) = names₂ := by
    rw [List.map_cons, List.map_append, List.map_append, e8, e2, names_blocks _ l h]
    rfl
  exact key

theorem shared_length (l : List (Block _root_.Desc.K14.St Unit)) (h : _root_.Desc.K14.blocks (p14At X P) = some l) (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (descriptionFromSource X N P).shared.blocksInOrder.length = 12 := by
  have := congrArg List.length (names₂_at X N P l h nO hO)
  rw [List.length_map] at this
  exact this

/-- **The last chain's.** -/
theorem names₃_at : (descriptionFromSource X N P).second.blocksInOrder.map (·.name) = names₃ := by
  obtain ⟨f, h, hn, -⟩ := second_flat X N P
  rw [h]
  have n2 : (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block _ Unit).name = "the proximity test (chain 3, piece 2)" := by
    rw [k12_name, p12At_place]
    decide
  show [f.name, "the taken trees' sources",
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block _ Unit).name, "the end of chain 3"] = names₃
  rw [hn, n2]
  rfl

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.names₂_at
#print axioms Johnson.RunOne.KeyRows23.names₃_at
#print axioms Johnson.RunOne.KeyRows23.shared_length
#print axioms Johnson.RunOne.KeyRows23.second_length
#print axioms Johnson.RunOne.KeyRows23.shared_flat
#print axioms Johnson.RunOne.KeyRows23.shared_at_blocks
#print axioms Johnson.RunOne.KeyRows23.second_flat
#print axioms Johnson.RunOne.KeyRows23.names_blocks
