-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/NoStrayLight.lean: kind K14: AT THE PUBLIC PART Z AND THE IOP F
THAT pubPlain AND onlineDescription RETURN AT THREE FILES, NO HALF OF THE LIST THAT THE FRAME's MAKER
nowSharedBy (Honest/AtPureWiderAt.lean) RETURNS STANDS AT A PLACE THAT F's SHARED CHAIN DOES NOT
HAVE, at every reader of the index: OVER FEW FILES. Statements with their proofs; no definition.

ONE STATEMENT UNDER A SECOND NAME. wider_k14_light has the statement of wider_k14
(Honest/K14/AtWiderShared.lean) to the letter. That theorem calls six_no_strays_made
(Honest/K14/NoStrayMade.lean), which stands, through one import (Honest/K14/AtFilling.lean), over
many files of which it reads two lemmas and an abbreviation. This file is for a caller whose imports
do not hold these: it imports none of the three.

  readers_light   where the library makes the places' numbers: what the filling's two readers
                  return. THE STATEMENT OF readers_at (Honest/K14/AtFilling.lean), with the body of
                  the library's abbreviation qAt (Johnson/Desc/K1/Law/SitsShared.lean) written out
                  in its stead, AND ITS PROOF, TYPED AGAIN; private
  flatOf_places_light   a list of the form FlatOf (Johnson/Desc/K14/Honest/FlatForm.lean) has a
                  member at each of the eight places. The statement of flatOf_places
                  (Honest/K14/NoStrayMade.lean); ANOTHER PROOF: off the form and the library's
                  own_places (Johnson/Desc/K14/Law/PlacesAtChain.lean), without tiedTo
  wider_k14_light   **the statement of the first sentence.** NO PREMISE BUT THE TWO EQUATIONS: where
                  the maker rejects the list is empty and the statement says nothing. THE PROOF IS
                  six_no_strays_made's, TYPED AGAIN behind one "show" (nowSharedBy's body); only
                  flatOf_places goes another way

What is not claimed. That pubPlain and onlineDescription return at any files. That the maker returns a half.
Nothing is said of what a half does. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.NoStray
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.K14.Honest.FlatPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block FileDescription)
open Desc.K14 (St blocks p14Of beforePointOf)
open Desc.K14.Honest (FlatOf flat_pure)
open Desc.K14.Law (seatN)

variable {Cl W₀ : Type}

/-- Where the library makes the places' numbers: what the filling's two readers return. -/
private theorem readers_light (Z : Pub) (N : H2U.Places4)
    (hN : H2U.placesOfMade Z.made = .ok N) :
    p14At Z = some (p14Of Z.p.chains (beforePointOf N)) ∧ onlineSharedChain Z = some (seatN Z N) := by
  constructor
  · unfold p14At
    rw [hN]
  · show Desc.K14.sharedSeatAt Z = _
    unfold Desc.K14.sharedSeatAt
    rw [hN]
    rfl

/-- A list of the form FlatOf has a member at each of the eight places. -/
theorem flatOf_places_light {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains}
    {P : Desc.K14.P14} {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) :
    ∀ a ∈ [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8],
      ∃ b ∈ xs, b.place = a := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, rfl, -, l1, l2, l3, l4, l5, l6, l7, l8⟩ := F
  have e8 : [b1, b2, b3, b4, b5, b6, b7, b8].map (·.place) =
      [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8] :=
    Desc.K14.Law.own_places P b1 b2 b3 b4 b5 b6 b7 b8 hb
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e8
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := e8
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨x1, by simp, l1.place.trans p1⟩
  · exact ⟨x2, by simp, l2.place.trans p2⟩
  · exact ⟨x3, by simp, l3.place.trans p3⟩
  · exact ⟨x4, by simp, l4.place.trans p4⟩
  · exact ⟨x5, by simp, l5.place.trans p5⟩
  · exact ⟨x6, by simp, l6.place.trans p6⟩
  · exact ⟨x7, by simp, l7.place.trans p7⟩
  · exact ⟨x8, by simp, l8.place.trans p8⟩

/-- **No half of nowSharedBy's list stands at a place that the shared chain does not have**, at what
pubPlain and onlineDescription return at three files, at every reader of the index. -/
theorem wider_k14_light {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {F : FileDescription Inst}
    (hZ : pubPlain o pol lay KL = .ok Z) (hF : onlineDescription o pol lay KL = .ok F)
    (weights : W₀ → Weights) :
    strays F.shared.blocksInOrder ((nowSharedBy weights Z).toOption.getD []) = [] := by
  obtain ⟨Z', N, B', c, hZ', hN, rfl, hfl⟩ := flat_pure hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain ⟨hP, hs⟩ := readers_light Z' N hN
  show strays _
    (((due? "the shared chain's own parameters" (p14At Z')).bind fun P =>
      (due? "the shared chain's place in the description" (onlineSharedChain Z')).bind fun s =>
        (sixOf P s.chain.blocksInOrder weights fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩ :
          Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)))
      ).toOption.getD []) = []
  rw [hP, hs]
  show strays _ ((sixOf (p14Of Z'.p.chains (beforePointOf N)) (seatN Z' N).chain.blocksInOrder weights _ :
    Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))).toOption.getD
      []) = []
  unfold sixOf
  cases hr : rejection (p14Of Z'.p.chains (beforePointOf N)) (seatN Z' N).chain.blocksInOrder with
  | some e => rfl
  | none =>
    cases dataOf (p14Of Z'.p.chains (beforePointOf N)).S (seatN Z' N).chain.blocksInOrder with
    | none => rfl
    | some d =>
      have ht := tied_of_pass (p14Of Z'.p.chains (beforePointOf N)) (seatN Z' N).chain.blocksInOrder hr
      unfold tiedTo at ht
      cases hb : blocks (p14Of Z'.p.chains (beforePointOf N)) with
      | none =>
        rw [hb] at ht
        cases ht
      | some l =>
        obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ :=
          Desc.K14.Law.eight (p14Of Z'.p.chains (beforePointOf N)) l hb
        exact strays_nil _ _ fun g hg =>
          flatOf_places_light hb (hfl b1 b2 b3 b4 b5 b6 b7 b8 hb).2 g.place
            (six_places d _ weights _ g hg)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.readers_light
#print axioms ProofFile.Honest.K14.flatOf_places_light
#print axioms ProofFile.Honest.K14.wider_k14_light
