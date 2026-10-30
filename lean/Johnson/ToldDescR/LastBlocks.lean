-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/LastBlocks.lean: no soundness is claimed.
The last chain's flat list at every description that onlineDescription makes, as a list of four named blocks, by make (LastPlaces.lean has their places; here the blocks themselves): for the join of the last chain's laws to the real description.
  p14At Z | ownAt N   the seat's letters, written out as the seat itself lays them (P2Third.secondSeatOf, Johnson/Desc/ProofFile/Lot/LastChain.lean) · secondSeatOf_chain: its chain is lastChainWithOwnTest at these letters: rfl
  laterSecondIs         laterSecond Z = some B → ∃ N, placesOfMade Z.made = .ok N ∧ B = P2Third.secondSeatOf Z N
  bare_eq               a block without claims and runs is what the flat list lays of it
  **last_blocks**       (lastChainWithOwnTest p own).blocksInOrder = [batchLinearConstraintsSecondPart p, takenSources own, own, end₃ [batchLinearConstraintsSecondPart p, takenSources own, own]], where own has neither claims nor runs and stands at chain 3, no link, piece 2
  **last_blocks_at**    the same at the seat: own := ownAt N = K12.Seat.onOwn (proximityTestKind guardedProximityTestParts (proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W))
  **last_blocks_in**    in the description: (fileDescBy o mk Z A (P2Third.secondSeatOf Z N) …).second.blocksInOrder = these four blocks, each carried by Block.retype (the frame lays the seat's chain by Chain.retype; Retype.lean: flat_retype)
  **second_descPure**   onlineDescription o pol lay KL = .ok F → ∃ Z N mk A c, pureRoad.pub o pol lay KL = .ok Z ∧ placesOfMade Z.made = .ok N ∧ F = fileDescBy o mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (startS Z) c
Why not by rfl. Chain.blocksInOrder lays each block outside the links as { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } (Block.lean:464), and the chain lays own as Third.ownAt own = { own with place := { own.place with chain := 3, link := none, piece := 2 } } (Johnson/Desc/Third/Chain.lean): the block itself, by two equations on values.
Who reads each letter. ∃ Z N mk A c: Z and N stand with their equations; mk A c in the one equation on F.
Does not show. Anything on what the blocks do. Nothing on soundness. (guardedProximityTestParts is one text in one module, Johnson/Desc/K12/JoinGuarded.lean: the kind's laws and this seat name the same constant.)
-/
import Johnson.ToldDescR.RcLastCode
import Johnson.ToldDescR.TiesAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ takenSources lastChainWithOwnTest batchLinearConstraintsSecondPart end₃
  p₁₄Z start₃F firstOfS sharedOfEnd fin₃)

/- `p14At`, K14's second part's parameters as the seat lays them, stands in RcLastCode.lean.
-/

/-- The request's own proximity test, seated. -/
def ownAt (N : H2U.Places4) : Block S₃ Unit :=
  onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W))

/-- The seat's chain, at the seat's name in its own file (`P2Third.secondSeatOf`,
Johnson/Desc/ProofFile/Lot/LastChain.lean).
-/
theorem secondSeatOf_chain (Z : ProofFile.Pub) (N : H2U.Places4) :
    (P2Third.secondSeatOf Z N).chain = lastChainWithOwnTest (p14At Z) (ownAt N) := rfl

theorem laterSecondIs {Z : ProofFile.Pub} {B : SecondSeat} (h : laterSecond Z = some B) :
    ∃ N, H2U.placesOfMade Z.made = .ok N ∧ B = P2Third.secondSeatOf Z N := by
  unfold laterSecond P2Third.secondSeat at h
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at h
    exact nomatch h
  | ok N =>
    rw [hN] at h
    exact ⟨N, rfl, (Option.some.inj h).symm⟩

/-- A block without claims and runs is what the flat list lays of it. -/
theorem bare_eq {σ Cl : Type} (b : Block σ Cl) (h : b.hasNoClaimsAndNothingAfter = true) :
    ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block σ Cl) = b := by
  rw [h, Bool.and_true]

/-- **The last chain's flat list, as four named blocks.** -/
theorem last_blocks {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (hb : own.hasNoClaimsAndNothingAfter = true)
    (hp : own.place = ⟨3, none, 2, own.place.kind⟩) :
    (lastChainWithOwnTest p own).blocksInOrder =
      [batchLinearConstraintsSecondPart p, takenSources own, own, end₃ [batchLinearConstraintsSecondPart p, takenSources own, own]] := by
  have e₂ : VerifiableInference.Desc.Third.ownAt own = own := by
    have : ({ own.place with chain := 3, link := none, piece := 2 } : Place) = own.place := hp.symm
    unfold VerifiableInference.Desc.Third.ownAt
    rw [this]
  have f : (lastChainWithOwnTest p own).blocksInOrder =
      [({ (batchLinearConstraintsSecondPart p : Block S₃ Cl) with
          planOk := (batchLinearConstraintsSecondPart p : Block S₃ Cl).planOk && (batchLinearConstraintsSecondPart p : Block S₃ Cl).hasNoClaimsAndNothingAfter }),
        ({ takenSources own with
          planOk := (takenSources own).planOk && (takenSources own).hasNoClaimsAndNothingAfter }),
        ({ VerifiableInference.Desc.Third.ownAt own with
          planOk := (VerifiableInference.Desc.Third.ownAt own).planOk &&
            (VerifiableInference.Desc.Third.ownAt own).hasNoClaimsAndNothingAfter }),
        ({ end₃ [batchLinearConstraintsSecondPart p, takenSources own, VerifiableInference.Desc.Third.ownAt own] with
          planOk :=
            (end₃ [batchLinearConstraintsSecondPart p, takenSources own,
              VerifiableInference.Desc.Third.ownAt own]).planOk &&
            (end₃ [batchLinearConstraintsSecondPart p, takenSources own,
              VerifiableInference.Desc.Third.ownAt own]).hasNoClaimsAndNothingAfter })] := rfl
  rw [f, e₂, bare_eq (batchLinearConstraintsSecondPart p) rfl, bare_eq (takenSources own) rfl,
    bare_eq (end₃ [batchLinearConstraintsSecondPart p, takenSources own, own]) rfl, bare_eq own hb]

theorem ownAt_place (N : H2U.Places4) : (ownAt N).place = ⟨3, none, 2, .K12⟩ := by
  show (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).place = _
  exact (k12_place _ _).trans (p12At_place _ _)

/-- **At the seat.** -/
theorem last_blocks_at (Z : ProofFile.Pub) (N : H2U.Places4) :
    (lastChainWithOwnTest (p14At Z) (ownAt N)).blocksInOrder =
      [batchLinearConstraintsSecondPart (p14At Z), takenSources (ownAt N), ownAt N,
        end₃ [batchLinearConstraintsSecondPart (p14At Z), takenSources (ownAt N), ownAt N]] :=
  last_blocks (p14At Z) (ownAt N) rfl (by rw [ownAt_place])

/-- **In the description**: the frame lays the seat's chain carried to the file's type of claims: its
flat list is these four blocks, each carried. -/
theorem last_blocks_in (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat)
    (N : H2U.Places4) (c : Chain S ProofFile.Cl) :
    (fileDescBy o mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (startS Z) c).second.blocksInOrder =
      [batchLinearConstraintsSecondPart (p14At Z), takenSources (ownAt N), ownAt N,
        end₃ [batchLinearConstraintsSecondPart (p14At Z), takenSources (ownAt N), ownAt N]].map Block.retype :=
  (flat_retype (lastChainWithOwnTest (p14At Z) (ownAt N)) rfl).trans
    (congrArg (List.map Block.retype) (last_blocks_at Z N))

/-- **At every description that `onlineDescription` makes**: its last chain is that seat's. -/
theorem second_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4) (mk : LinksBy) (A : SharedSeat) (c : Chain S ProofFile.Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
        F = fileDescBy o mk Z A (P2Third.secondSeatOf Z N) (fun s => s) (startS Z) c := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, -, hB, rfl⟩ := pureZ_make h
  have hB' : laterSecond Z = some B := hB
  obtain ⟨N, hN, rfl⟩ := laterSecondIs hB'
  exact ⟨Z, N, _, A, c, hZ, hN, rfl⟩

end ToldDesc

#print axioms ToldDesc.laterSecondIs
#print axioms ToldDesc.bare_eq
#print axioms ToldDesc.last_blocks
#print axioms ToldDesc.last_blocks_at
#print axioms ToldDesc.last_blocks_in
#print axioms ToldDesc.second_descPure
