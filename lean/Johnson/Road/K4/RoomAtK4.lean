-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RoomAtK4.lean: THE NAME "pile.room" AT K4's TWO BORDERS, AT THE WIDER MEANING's LIST
OF EXTRA PUBLIC TESTS OVER THE CLOSED BASE: at which segment's number it is open in front of and
behind K4's sub-protocol (by Lean's kernel, at the written lists), and, at the reached states of
these two borders, the clause on it that the tight form of the bridge's premise asks (the premise hR
of factsAt_at, Johnson/Desc/Sound/MgWideFacts.lean: NOT IMPORTED:
its text is stated), out of ONE premise: the test at the reached states IN FRONT of K4's
sub-protocol, at the segment's own number.

  `roomOpenFit`, `room_of_fit`: the test and what an accept gives at a place of K4's.
  `room_open_wide`: it accepts at moreWideAll, at the full lists: by the kernel. `room_is_open`: the
    name IS open at the segment's own number at both borders, ×12. `room_open_other`: A NEGATIVE
    TEST: asked for the segment after next, the test rejects ×12.
  `RoomAt M E j s`: the clause at border j and state s: the text of hR behind its "no mark".
  **`hR_at_k4`**: in the goals' scope, at an opening, g < 12, under R0: RoomAt at every state
    without a mark that is reached at border 28 g + 4, and at every such state reached at border
    28 g + 5. R0 and both ends are fenced to a state without a mark (the payers'
    facts are so fenced); an accept of K4's leaves the mark as it was.
Across K4's own piece the test is kept: kept_rchAt (Johnson/Road/K4/K8OpenAtK4.lean) and
roomIsB_kept (Johnson/Road/K4/Riders/KeepsOfMeans.lean).
Limits. THE WIDER MEANING IS A BRIDGE's SIDE. R0 is shown by nobody here. That there is an opening
is shown by no theorem. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.


-/
import Johnson.Road.K4.K8OpenAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Road.K4.Riders (atK4s atK4s_at roomIsB_kept)
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart More Pub pubSets flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull moreWideAll MgData WideData mgBase moreW moreW_base)
open Johnson.Desc.First.Walk.Tied (RchAt roomIsB)

/-- At every place of K4's, at both borders: "pile.room" is open at the segment's own number
alone. -/
def roomOpenFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k m =>
    (((pubSets M links ps)[k]?.getD []).all fun q =>
      !nameIs q "pile.room" || q == .more (some m) "pile.room") &&
    (((pubSets M links ps)[k + 1]?.getD []).all fun q =>
      !nameIs q "pile.room" || q == .more (some m) "pile.room")

variable {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- What an accept gives at a place of K4's. -/
theorem room_of_fit (H : AtK4 links ps k m pl) (h : roomOpenFit M links ps = true) :
    (∀ m', Pub.more (some m') "pile.room" ∈ (pubSets M links ps)[k]?.getD [] → m' = m) ∧
      ∀ m', Pub.more (some m') "pile.room" ∈ (pubSets M links ps)[k + 1]?.getD [] → m' = m := by
  have h1 := atK4s_at (t := fun k m =>
    (((pubSets M links ps)[k]?.getD []).all fun q =>
      !nameIs q "pile.room" || q == .more (some m) "pile.room") &&
    (((pubSets M links ps)[k + 1]?.getD []).all fun q =>
      !nameIs q "pile.room" || q == .more (some m) "pile.room")) H h
  rw [Bool.and_eq_true] at h1
  obtain ⟨a, b⟩ := h1
  refine ⟨fun m' hm => ?_, fun m' hm => ?_⟩
  · have := List.all_eq_true.1 a _ hm
    simpa [nameIs] using this
  · have := List.all_eq_true.1 b _ hm
    simpa [nameIs] using this

set_option maxRecDepth 1000000 in
theorem room_open_wide :
    roomOpenFit moreWideAll linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The name is open at the segment's own number at both borders**, ×12. -/
theorem room_is_open :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      ((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k]?.getD []).contains
          (.more (some m) "pile.room") &&
        ((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k + 1]?.getD []).contains
          (.more (some m) "pile.room")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: asked for the segment after next, the test rejects, ×12. -/
theorem room_open_other :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      !(((pubSets moreWideAll linksFull (flatPlacesOf linksFull true))[k]?.getD []).all fun q =>
        !nameIs q "pile.room" || q == .more (some (m + 2)) "pile.room")) = true := by
  decide +kernel

/-- The clause at border j and state s. -/
def RoomAt {P : Type} (M : More) (E : WideData P) (j : ℕ) (s : S) : Prop :=
  ∀ m, Pub.more (some m) "pile.room" ∈
      (pubSets M linksFull (flatPlacesOf linksFull true))[j]?.getD [] →
    roomIsB E.dP.free0 E.dP.fvs m s = true

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ}

/-- **The clause at the reached states of K4's two borders, out of the test in front.** -/
theorem hR_at_k4 {Xi Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR X) (E : WideData ProofFile.InstPub)
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {Str : Type}
    (R0 : ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
      RchAt (descAt Z A B c) (28 * g + 4) a → S.failed a.1.2 = none →
        roomIsB E.dP.free0 E.dP.fvs (2 * g) a.1.2 = true) :
    (∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) (28 * g + 4) a → S.failed a.1.2 = none →
          RoomAt (moreW Dm mgBase) E (28 * g + 4) a.1.2) ∧
      ∀ a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str,
        RchAt (descAt Z A B c) (28 * g + 5) a → S.failed a.1.2 = none →
          RoomAt (moreW Dm mgBase) E (28 * g + 5) a.1.2 := by
  rw [moreW_base]
  obtain ⟨a1, a2⟩ := room_of_fit (atK4_full g hg) room_open_wide
  refine ⟨fun a h hu m' hm => ?_, fun a h hu m' hm => ?_⟩
  · rw [a1 m' hm]
    exact R0 a h hu
  · rw [a2 m' hm]
    obtain ⟨s, p, hr, K⟩ := kept_rchAt hS hR O hg h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hRest, _⟩ := K
    rw [roomIsB_kept hRest]
    exact R0 _ hr (hRest.failed.symm.trans hu)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.room_of_fit
#print axioms OnBytes.Road.K4.room_open_wide
#print axioms OnBytes.Road.K4.room_is_open
#print axioms OnBytes.Road.K4.room_open_other
#print axioms OnBytes.Road.K4.hR_at_k4
