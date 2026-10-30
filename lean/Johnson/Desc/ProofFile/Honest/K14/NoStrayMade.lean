-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/NoStrayMade.lean: kind K14: NO HALF OF THE SHARED CHAIN's HALVES,
AS TWO MAKERS OF A FILLING LAY THEM, STANDS AT NO PLACE OF THE SHARED CHAIN OF THE IOP AS WRITTEN IN
LEAN THAT THE LIBRARY's onlineDescription RETURNS. Statements with their proofs; no definition. In both
statements strays is asked of F.shared.blocksInOrder, the chain CARRIED to the description's type of claims,
while the makers read the PLAIN chain's list: two lists: so six_no_strays
(Honest/K14/NoStray.lean), which speaks of one list, is not what is called here.

  flatOf_places   a list of the form FlatOf (Johnson/Desc/K14/Honest/FlatForm.lean) has a member at
                  each of the eight places: tied_places after tiedTo_flat (Honest/K14/DataMade.lean)
  six_no_strays_made   **at the public part Z and the IOP F that pubPlain and onlineDescription return at
                  three files: the halves that sixOf returns at the shared chain's own parameters
                  (p14At Z) and at the library's own list for that chain (onlineSharedChain Z)**, at any
                  reader of the index and at the plan's item's pads and tails. THE TERM IS WRITTEN
                  OUT: it is the body of the frame's nowSharedBy (Honest/AtPureWiderAt.lean), which
                  is not imported here: that file stands over all kinds' halves. NO PREMISE BUT THE
                  TWO EQUATIONS: where sixOf rejects there is no half
  inFront_none    no sub-protocol at a place: roundsInFront returns nothing
  now_rejects     where the library makes no eight sub-protocols of the plan, nowShared returns no
                  half: "LIN zeta"'s place is the place of no member of the chain's list (by the
                  library's tests_places, tests_places_none and last_place,
                  Johnson/Desc/K12/Law/SharedPlaces.lean)
  now_no_strays   **the same at nowShared Z** (Honest/SharedChainProverSides.lean), which evaluates none of
                  sixOf's tests: NO PREMISE BUT THE TWO EQUATIONS: by a split on whether the library
                  makes its eight

What is not claimed. That pubPlain and onlineDescription return at any files. That either maker returns a
half. That the written term is nowSharedBy's body: to be held where that file is imported. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.NoStray
import Johnson.Desc.ProofFile.Honest.K14.AtFilling
import Johnson.Desc.K14.Honest.FlatPure
import Johnson.Desc.K12.Law.SharedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place FileDescription)
open VerifiableInference.Desc.K12.Seat (tests last)
open Desc.K14 (St blocks chainOf)
open Desc.K14.Honest (FlatOf flat_pure)
open Desc.K14.Law (seatN)

variable {S Cl W₀ : Type}

/-- A list of the form FlatOf has a member at each of the eight places. -/
theorem flatOf_places {xs : List (Block St Cl)} {c : OnBytes.Model.Verify.Chains}
    {P : Desc.K14.P14} {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit}
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (F : FlatOf xs c b1 b2 b3 b4 b5 b6 b7 b8) :
    ∀ a ∈ [place 1, sendPlace 2, place 3, place 4, sendPlace 5, place 6, place 7, place 8],
      ∃ b ∈ xs, b.place = a := tied_places P xs (tiedTo_flat F hb)

/-- **At what pubPlain and onlineDescription return: the halves that sixOf returns at the filling's own two
readers.** -/
theorem six_no_strays_made {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    {F : FileDescription Inst} (hZ : pubPlain o pol lay KL = .ok Z) (hF : onlineDescription o pol lay KL = .ok F)
    (weights : W₀ → Weights) :
    strays F.shared.blocksInOrder
      (((due? "the shared chain's own parameters" (p14At Z)).bind fun P =>
        (due? "the shared chain's place in the description" (onlineSharedChain Z)).bind fun s =>
          (sixOf P s.chain.blocksInOrder weights fun rc : IndexCommitterCoins => ⟨(rc P.item).pad, (rc P.item).tail⟩ :
            Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)))
        ).toOption.getD []) = [] := by
  obtain ⟨Z', N, B', c, hZ', hN, rfl, hfl⟩ := flat_pure hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  obtain ⟨hP, hs⟩ := readers_at Z' N hN
  rw [hP, hs]
  show strays _ ((sixOf (qAt Z' N) (seatN Z' N).chain.blocksInOrder weights _ :
    Except String (List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit))).toOption.getD
      []) = []
  unfold sixOf
  cases hr : rejection (qAt Z' N) (seatN Z' N).chain.blocksInOrder with
  | some e => rfl
  | none =>
    have ht := tied_of_pass (qAt Z' N) (seatN Z' N).chain.blocksInOrder hr
    cases dataOf (qAt Z' N).S (seatN Z' N).chain.blocksInOrder with
    | none => rfl
    | some d =>
      unfold tiedTo at ht
      cases hb : blocks (qAt Z' N) with
      | none =>
        rw [hb] at ht
        cases ht
      | some l =>
        obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.eight (qAt Z' N) l hb
        exact strays_nil _ _ fun g hg =>
          flatOf_places hb (hfl b1 b2 b3 b4 b5 b6 b7 b8 hb).2 g.place
            (six_places d _ weights _ g hg)

/-- No sub-protocol at a place: roundsInFront returns nothing. -/
theorem inFront_none : ∀ (bs : List (Block S Cl)) (a : Place), (∀ b ∈ bs, b.place ≠ a) →
    roundsInFront bs a = none
  | [], _, _ => rfl
  | b :: bs, a, h => by
    have h1 : (b.place == a) = false := beq_eq_false_iff_ne.2 (h b List.mem_cons_self)
    show (if (b.place == a) = true then some 0
      else (roundsInFront bs a).map (· + b.rounds.length)) = none
    rw [h1, if_neg Bool.false_ne_true,
      inFront_none bs a fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- **Where the library makes no eight sub-protocols of the plan, nowShared returns no half.** -/
theorem now_rejects (Z : Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N)
    (hb : blocks (qAt Z N) = none) : (nowShared Z).toOption = none := by
  obtain ⟨hP, hs⟩ := readers_at Z N hN
  have hpl : ∀ b ∈ (seatN Z N).chain.blocksInOrder, b.place ≠ place 7 := by
    intro b hbm
    have hm : b.place ∈ (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder.map (·.place) :=
      List.mem_map.2 ⟨b, hbm, rfl⟩
    have hl : (chainOf Z.p.chains (qAt Z N) (tests N) last).blocksInOrder.map (·.place) =
        ⟨2, none, 0, .frame⟩ :: ⟨2, none, 1, .frame⟩ ::
          ((tests N).map (·.place) ++ [⟨2, none, 11, .frame⟩]) := by
      simp [chainOf, Desc.K14.blocksOr, hb, VerifiableInference.Desc.Chain.blocksInOrder,
        Desc.K14.frontBlock, VerifiableInference.Desc.roundlessBlock,
        H2K.JointK.last_place, Function.comp_def]
    rw [hl] at hm
    intro e
    rw [e] at hm
    cases hO : N.O with
    | none =>
      rw [H2K.JointK.tests_places_none N hO] at hm
      simp [place] at hm
    | some nO =>
      rw [H2K.JointK.tests_places N nO hO] at hm
      simp [place] at hm
  have hz : sharedInFront Z (place 7) = none := by
    unfold sharedInFront
    rw [hs]
    exact inFront_none _ _ hpl
  unfold nowShared
  rw [hP, hz]
  cases sharedInFront Z (place 1) <;> rfl

/-- **The same at nowShared: no premise but the two equations.** -/
theorem now_no_strays {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub} {F : FileDescription Inst}
    (hZ : pubPlain o pol lay KL = .ok Z) (hF : onlineDescription o pol lay KL = .ok F) :
    strays F.shared.blocksInOrder ((nowShared Z).toOption.getD []) = [] := by
  obtain ⟨Z', N, B', c, hZ', hN, rfl, hfl⟩ := flat_pure hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans hZ)
  cases hb : blocks (qAt Z' N) with
  | none =>
    rw [now_rejects Z' N hN hb]
    rfl
  | some l =>
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.eight (qAt Z' N) l hb
    refine strays_nil _ _ fun g hg =>
      flatOf_places hb (hfl b1 b2 b3 b4 b5 b6 b7 b8 hb).2 g.place ?_
    unfold nowShared at hg
    cases hP : p14At Z' with
    | none =>
      rw [hP] at hg
      cases hg
    | some P =>
      rw [hP] at hg
      cases ha : sharedInFront Z' (place 1) with
      | none =>
        rw [ha] at hg
        cases hg
      | some a =>
        rw [ha] at hg
        cases hz : sharedInFront Z' (place 7) with
        | none =>
          rw [hz] at hg
          cases hg
        | some z =>
          rw [hz] at hg
          exact six_places _ _ id _ g hg

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.flatOf_places
#print axioms ProofFile.Honest.K14.six_no_strays_made
#print axioms ProofFile.Honest.K14.inFront_none
#print axioms ProofFile.Honest.K14.now_rejects
#print axioms ProofFile.Honest.K14.now_no_strays
