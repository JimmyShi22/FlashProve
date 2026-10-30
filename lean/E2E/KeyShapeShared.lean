--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeShared.lean: THE KEY FILE's SHARED CHAIN's TWO PROXIMITY TESTS (on G_u; on G_omega) ON
SHAPES: ONE DIRECTION: (B1) of Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's cut. Where a seated
test accepts, the test on the core's shape (`testCore`, Johnson/Desc/K12/Honest/Shape/TestCore.lean)
returns the core's shape behind, and the chain's named values stay. Statements and proofs. Steps of
the verifier's: NOTHING IS SHOWN OF ANY PROVER.

  `seat_inv`: a seated test's accept, read back, at whichever group and mask the seat reads.
  **`seat_core`**: (B1) on the core's shape; the named values and the columns read stay.
  `seat_mark`, `seat_codes`: the mark on the statement is kept (the library's `seat_tidy`); so are
    the codes.
  **`gu_core`**, **`gomega_core`**: at the two seats.
  **`shared_places_in_scope`**: under `KeySourced` (E2E/KeyPublic.lean) and `VerifierAndGoals.InScope Z` both
    places meet the law's two conditions (masks are sent ahead; one answer to a sample).

Limits.
- (B2) IS NOT HERE: `testCore` asks fewer guards than the test.
- The shared chain's shape is another hand's; the laws are stated at the chain's state and the
  core's shape. The chain's eight other sub-protocols, its front and its end are not here.


-/
import E2E.KeyShapeOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open ProofFile.Honest.Sh (testCore k12_core_sh)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open _root_.Desc.K14 (St Lin)

/-- A seated test's accept, read back. -/
theorem seat_inv (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs =
        .ok d') :
    ∃ tE : T12, (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
        { st := d.st, book := d.book, roots := d.roots, g := g d.loc, pass := .nothing
          mask := mask d.loc } rs gs = .ok tE ∧
      d' = { d with st := tE.st, book := tE.book, roots := tE.roots } := by
  have h' : ((proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
      { st := d.st, book := d.book, roots := d.roots, g := g d.loc, pass := .nothing
        mask := mask d.loc } rs gs).bind (VerifiableInference.Desc.K12.Seat.leave d) = .ok d' := h
  cases hk : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).decide
      { st := d.st, book := d.book, roots := d.roots, g := g d.loc, pass := .nothing
        mask := mask d.loc } rs gs with
  | error e =>
    rw [hk] at h'
    cases h'
  | ok tE =>
    rw [hk] at h'
    exact ⟨tE, rfl, (Except.ok.inj h').symm⟩

/-- **(B1) on the core's shape.** -/
theorem seat_core (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (he : p.early = true)
    (ha : p.answers = 1) (d d' : St) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs =
        .ok d') :
    testCore p (coreSh ⟨d.st, d.book, d.roots⟩) (g d.loc) (mask d.loc) =
        some (coreSh ⟨d'.st, d'.book, d'.roots⟩) ∧ d'.loc = d.loc ∧ d'.opened = d.opened := by
  obtain ⟨tE, hk, rfl⟩ := seat_inv g mask p d d' rs gs h
  have c : testCore p (coreSh ⟨d.st, d.book, d.roots⟩) (g d.loc) (mask d.loc) =
      some (coreSh ⟨tE.st, tE.book, tE.roots⟩) :=
    k12_core_sh p he ha { st := d.st, book := d.book, roots := d.roots, g := g d.loc
                          pass := .nothing, mask := mask d.loc } tE rs gs hk
  exact ⟨c, rfl, rfl⟩

/-- The mark on the statement is kept. -/
theorem seat_mark (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs =
        .ok d') (hl : d.st.codes.lengthsOk = true) (hT : stTidyB d.st = true) :
    stTidyB d'.st = true :=
  tidy_mark (VerifiableInference.Desc.K12.Coin.seat_tidy g mask p d d' rs gs h hl (tidy_of hT))

/-- So are the codes. -/
theorem seat_codes (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Block.inside (VerifiableInference.Desc.K12.Seat.enter g mask)
      (proximityTestKind guardedProximityTestParts p : Block T12 Unit) VerifiableInference.Desc.K12.Seat.leave).decide d rs gs =
        .ok d') : d'.st.codes = d.st.codes := by
  obtain ⟨tE, hk, rfl⟩ := seat_inv g mask p d d' rs gs h
  exact (H2K.Out.k12_grows p _ tE rs gs hk).1

/-- **At the test on G_u.** -/
theorem gu_core (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d') :
    testCore p (coreSh ⟨d.st, d.book, d.roots⟩) d.loc.gU d.loc.firstMask =
        some (coreSh ⟨d'.st, d'.book, d'.roots⟩) ∧ d'.loc = d.loc ∧ d'.opened = d.opened :=
  seat_core (·.gU) (·.firstMask) p he ha d d' rs gs h

/-- **At the test on G_omega**: the seat hands the test no mask's number. -/
theorem gomega_core (p : P12) (he : p.early = true) (ha : p.answers = 1) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p)).decide d rs gs = .ok d') :
    testCore p (coreSh ⟨d.st, d.book, d.roots⟩) d.loc.gOmega none =
        some (coreSh ⟨d'.st, d'.book, d'.roots⟩) ∧ d'.loc = d.loc ∧ d'.opened = d.opened :=
  seat_core (·.gOmega) (fun _ => none) p he ha d d' rs gs h

/-- **In scope both places meet the two conditions.** -/
theorem shared_places_in_scope {Z : VerifierAndGoals.PublicFiles} {X : VerifiableInference.Desc.Key.Source}
    {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces} (hs : KeySourced Z X N P)
    (scope : VerifierAndGoals.InScope Z = true) :
    ((H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).answers = 1) ∧
    ∀ nO, P.O = some nO → (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).early = true ∧
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).answers = 1 := by
  obtain ⟨X₀, m, h0, hm, hX, -, hP⟩ := hs.source
  have hR := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0
  have hk := Johnson.RunOne.Law.KeyInScope.key_in_scope scope hR hm
  have hset : m.p.chains.made.sized.set = H2K.Member.setAt :=
    (Johnson.RunOne.Law.K12Facts15.set_in_scope scope hR hm).trans (by decide +kernel)
  have hL := H2K.Sizes.later_of_full hk hset hP
  refine ⟨?_, fun nO hO => ?_⟩
  · obtain ⟨-, -, -, -, -, e6, e7⟩ := hL.1
    obtain ⟨a, b⟩ := p12At_fields (Cl := Unit) ⟨2, none, 9, .K12⟩ P.U
      (H2K.JointK.keyPlan_U X N P hs.named.plan)
    exact ⟨b.trans (e7.trans (by decide +kernel)), a.trans (e6.trans (by decide +kernel))⟩
  · obtain ⟨-, -, -, -, -, e6, e7⟩ := hL.2.2 nO hO
    obtain ⟨a, b⟩ := p12At_fields (Cl := Unit) ⟨2, none, 10, .K12⟩ nO
      (H2K.JointK.keyPlan_O X N P hs.named.plan nO hO)
    exact ⟨b.trans (e7.trans (by decide +kernel)), a.trans (e6.trans (by decide +kernel))⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.seat_inv
#print axioms AtPublicFiles.AtFiles.seat_core
#print axioms AtPublicFiles.AtFiles.seat_mark
#print axioms AtPublicFiles.AtFiles.seat_codes
#print axioms AtPublicFiles.AtFiles.gu_core
#print axioms AtPublicFiles.AtFiles.gomega_core
#print axioms AtPublicFiles.AtFiles.shared_places_in_scope
