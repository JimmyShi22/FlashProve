-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyValueHolds.lean: at the written value of the key file's prover's senders with the four proximity tests in
place, the tests on places and stops that a theorem on the prover asks: the halves stand at the key file's places,
no part ever stops, and a half stands at every sub-protocol that sends. By text.

Why. `noStopAll_keyProver` (E2E/KeyNoStop.lean), `halvedAll_key` (E2E/KeyLaid.lean) and the accept laws take these
as premises at letters. Here the letters are the terms of E2E/KeyFifteen.lean, E2E/KeyArgumentsAt.lean and IOP's
`withTests`, so the premises fall away but for those that read the public files.

Main names.
  `quietHalf_test`, `quietHalf_needs`: a proximity test's half has no stop, and the guard adds none.
  `rooted_of_rows`, `rooted_sealed`, `rootedAll_key`: a half stands at every sub-protocol that sends a root.
  `valueAt`: the value: `withTests` over `withStoredColumnsAndPlan` over `withSendingsAndLookups`.
  `atPlaces_value`: `KeyParts.AtPlaces` at it, the seven equations.
  `atAll_value`: `KeyParts.AtAll` at it.
  `noStop_value`: `NoStopAll` at its `keyProver`.
  `noSecond_value`: at the first and the last chain no part has a stop that reads the private input.
  `halved_value`, `rooted_value`: `halvedAll` and `rootedAll` at the key file's description.

What stays open. Three premises, on public values: `hW`: the shape has a message W (elsewhere `batchedRowsSending` is a stand-in
at the index masks' place); `hsp`: the shape splits; scope and `KeyNamed` for the last two theorems. That `look0`
and `look1` bear the book's two faces is not asked by `AtPlaces` and is not said here. A quiet part says that the
honest side always sends; it says nothing on whether a verifier accepts. Nothing here reads what a half sends.

No statement here names a coin. No law over coins.

Nothing on soundness, completeness, hiding or binding.

`place_p12At` holds at either arm of `proximityTestParametersAt`, so these statements hold at any value of the test's numbers: they say nothing on
whether the four tests are the real ones.

-/
import E2E.KeyNoStop
import E2E.KeyLaid
import E2E.KeyArgumentsAt
import Johnson.Desc.ProofFile.Honest.Law.PlanGives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeyValueHolds
open ProofFile.Honest
open ProofFile.Honest.K12 (TestJob proverSideOfProximityTest firstPart restPart)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi pieces)
open OnBytes.Slice (GF)
open AtPublicFiles.Stops (QuietHalf Quiet NoStopAll)
open AtPublicFiles.KeyLink (any_places)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyFile (KeyParts keyProver first_places keyProver_shared halvedAll_key
  noStopAll_keyProver)
open AtPublicFiles.KeyBook (foldedTestPlace omegaTestPlace)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open AtPublicFiles.AtFiles.HonestTerm (withStoredColumnsAndPlan)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups oneOf)
open AtPublicFiles.KeyLay (withTests pWK)
open VerifierAndGoals (PublicFiles InScope)

/-- The number of a place is the one that `proximityTestParametersAt` is handed, at either of its arms. -/
theorem place_p12At (a : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

section Quiet
variable {V W X : Type}

/-- **A proximity test's half has no stop.** On the two parts' texts. -/
theorem quietHalf_test (J : TestJob W X) : QuietHalf (proverSideOfProximityTest J : Placed V W X) := by
  intro p hp
  have hp' : p ∈ [(firstPart J : Part V W X), restPart J] := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · unfold firstPart
    split
    · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
    · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  · exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The guard adds no stop**: it turns a part's moves alone. -/
theorem quietHalf_needs {h : Placed V W X} (hq : QuietHalf h) : QuietHalf h.needsField := by
  intro p hp
  obtain ⟨q, hq', rfl⟩ := List.mem_map.1 hp
  exact hq q hq'

end Quiet

section Rooted
variable {S Cl V W Y : Type}

/-- From the rows: a sub-protocol without a round passes; one with rounds wants a half. -/
theorem rooted_of_rows (bs : List (Block S Cl)) (hs : List (Placed V W Y))
    (rows : List (Place × Nat)) (hr : rowsOf bs = rows)
    (hall : ∀ r ∈ rows, r.2 = 0 ∨ ((hs.map (·.place)).any (· == r.1)) = true) :
    rooted bs hs = true := by
  unfold rooted
  rw [List.all_eq_true]
  intro b hb
  have hm : (b.place, b.rounds.length) ∈ rows := by
    rw [← hr]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  rcases hall _ hm with h0 | h1
  · rw [List.eq_nil_of_length_eq_zero h0]
    exact Bool.or_true _
  · rw [any_places, h1]
    rfl

/-- The like for a chain whose last sub-protocol's rounds send no root. -/
theorem rooted_sealed (c : Chain S Cl) (hs : List (Placed V W Y)) (rows : List (Place × Nat))
    (e : Place × Nat) (hr : rowsOf c.blocksInOrder = rows ++ [e])
    (hl : (c.last.rounds.all fun d => d.entry.roots == 0) = true)
    (hall : ∀ r ∈ rows, r.2 = 0 ∨ ((hs.map (·.place)).any (· == r.1)) = true) :
    rooted c.blocksInOrder hs = true := by
  obtain ⟨A, hA⟩ : ∃ A, c.blocksInOrder = A ++ [{ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }] :=
    ⟨_, rfl⟩
  rw [hA] at hr ⊢
  unfold rowsOf at hr
  rw [List.map_append] at hr
  have hA' : rowsOf A = rows := (List.append_inj' hr rfl).1
  have h1 := rooted_of_rows A hs rows hA' hall
  unfold rooted at h1 ⊢
  rw [List.all_append, h1, Bool.true_and, List.all_cons, List.all_nil, Bool.and_true]
  have hl' : (({ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter } : Block S Cl).rounds.all
      fun d => d.entry.roots == 0) = true := hl
  rw [hl']
  exact Bool.or_true _

end Rooted

section AtAll
variable {W₀ Rc X₀ X Wk : Type}

/-- **In scope a half of `keyProver K` stands at every sub-protocol of the key file that sends a root.** The
proof of `halvedAll_key`, at `rooted`. -/
theorem rootedAll_key {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (scope : InScope Z = true) (h : KeyNamed Z Xs N P) (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) :
    rootedAll (keyFileDescription Xs N P) (keyProver K) = true := by
  obtain ⟨r1, r2, r3⟩ := AtPublicFiles.KeyBook.places_named scope h
  have e1 : AtPublicFiles.KeyBook.fullFirst = ([(AtPublicFiles.KeyBook.idxPlace, 2), (AtPublicFiles.KeyBook.msgPlace, 2)] ++
                AtPublicFiles.KeyBook.linkRows 0 9581 ++ AtPublicFiles.KeyBook.linkRows 1 9220 ++
                [(AtPublicFiles.KeyBook.rowsPlace, 0), (AtPublicFiles.KeyBook.rngPlace, 23), (AtPublicFiles.KeyBook.battPlace, 20),
                  (AtPublicFiles.KeyBook.wPlace, 2)]) ++ [(AtPublicFiles.KeyBook.sealPlace, 1)] := by
    decide
  have e2 : AtPublicFiles.KeyBook.fullShared = [(AtPublicFiles.KeyBook.frontPlace, 0), (AtPublicFiles.KeyBook.pointPlace, 1),
                (AtPublicFiles.KeyBook.foldedPlace, 2), (AtPublicFiles.KeyBook.gammaPlace, 0), (AtPublicFiles.KeyBook.locPlace, 1),
                (AtPublicFiles.KeyBook.omegaPlace, 2), (AtPublicFiles.KeyBook.joinsPlace, 0), (AtPublicFiles.KeyBook.zetaPlace, 1),
                (AtPublicFiles.KeyBook.splitPlace, 1), (foldedTestPlace, 35), (omegaTestPlace, 24)] ++
      [(AtPublicFiles.KeyBook.sharedSealPlace, 1)] := by decide
  have a1 : rooted (keyFileDescription Xs N P).first.blocksInOrder (keyProver K).first = true :=
    rooted_sealed _ _ _ _ (r1.trans e1) rfl (by
      rw [first_places K hK.first]
      decide)
  have a2 : rooted (keyFileDescription Xs N P).shared.blocksInOrder (keyProver K).shared = true :=
    rooted_sealed _ _ _ _ (r2.trans e2) rfl (by
      rw [keyProver_shared K hK.splits, hK.onU, hK.onOmega]
      decide)
  have a3 : rooted (keyFileDescription Xs N P).second.blocksInOrder (keyProver K).second = true :=
    rooted_of_rows _ _ _ r3 (by
      show ∀ r ∈ AtPublicFiles.KeyBook.fullSecond, r.2 = 0 ∨ (([K.own].map (·.place)).any (· == r.1)) = true
      rw [List.map_cons, List.map_nil, hK.own]
      decide)
  unfold rootedAll
  rw [a1, a2, a3]
  rfl

end AtAll

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The value**: the fifteen, then `withStoredColumnsAndPlan`'s five, then the four proximity tests. -/
abbrev valueAt : KeyParts W₀ Rc Unit Unit WitK :=
  withTests (withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs N f inR d) f g) Xs N Pl pU pO ent groups first

/-- **The seven equations of `KeyParts.AtPlaces`.** hW: the shape has a message W. -/
theorem atPlaces_value (hW : (OnBytes.linMessageW (oneOf Xs).lin).isSome = true) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtPlaces := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, ?_⟩
  · exact place_p12At _ _
  · obtain ⟨msg, hm⟩ := Option.isSome_iff_exists.1 hW
    show (AtPublicFiles.KeyValues.batchedRowsSending f Xs N).P.place = _
    unfold AtPublicFiles.KeyValues.batchedRowsSending AtPublicFiles.Key.wJob
    rw [hm]
    rfl

/-- **The letters bear the sixteen places.** hsp: the shape splits. hU, hO: the two places' numbers are at their
places. -/
theorem atAll_value (hW : (OnBytes.linMessageW (oneOf Xs).lin).isSome = true)
    (hsp : (ProofFile.Honest.K14.planData (AtPublicFiles.KeySharedThread.parKey Xs Pl)).S.sharedSplitNeeded = true)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) :
    (valueAt K' Xs N Pl f g inR d pU pO ent groups first).AtAll :=
  ⟨atPlaces_value K' Xs N Pl f g inR d pU pO ent groups first hW, hsp, hU, hO, place_p12At _ _⟩

/-- **No part of the value's `keyProver` ever stops.** -/
theorem noStop_value :
    NoStopAll (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) :=
  noStopAll_keyProver _ (quietHalf_test _) (quietHalf_test _) (quietHalf_needs (quietHalf_test _))
    (quietHalf_needs (quietHalf_test _))

/-- **At the first and the last chain no part has a stop that reads the private input.** -/
theorem noSecond_value :
    (∀ h ∈ (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).first, ∀ p ∈ h.parts,
        ∀ v o q, p.hid v o q = none) ∧
      ∀ h ∈ (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)).second,
        ∀ p ∈ h.parts, ∀ v o q, p.hid v o q = none :=
  ⟨fun h hh p hp => ((noStop_value K' Xs N Pl f g inR d pU pO ent groups first).1 h hh p hp).2,
    fun h hh p hp => ((noStop_value K' Xs N Pl f g inR d pU pO ent groups first).2.2 h hh p hp).2⟩

variable {Z : PublicFiles}

/-- **In scope a half stands at every sub-protocol that sends.** -/
theorem halved_value (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (hW : (OnBytes.linMessageW (oneOf Xs).lin).isSome = true)
    (hsp : (ProofFile.Honest.K14.planData (AtPublicFiles.KeySharedThread.parKey Xs Pl)).S.sharedSplitNeeded = true)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) :
    halvedAll (keyFileDescription Xs N Pl)
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) = true :=
  halvedAll_key scope h _ (atAll_value K' Xs N Pl f g inR d pU pO ent groups first hW hsp hU hO)

/-- **And at every one that sends a root.** -/
theorem rooted_value (scope : InScope Z = true) (h : KeyNamed Z Xs N Pl)
    (hW : (OnBytes.linMessageW (oneOf Xs).lin).isSome = true)
    (hsp : (ProofFile.Honest.K14.planData (AtPublicFiles.KeySharedThread.parKey Xs Pl)).S.sharedSplitNeeded = true)
    (hU : pU.place = foldedTestPlace) (hO : pO.place = omegaTestPlace) :
    rootedAll (keyFileDescription Xs N Pl)
      (keyProver (valueAt K' Xs N Pl f g inR d pU pO ent groups first)) = true :=
  rootedAll_key scope h _ (atAll_value K' Xs N Pl f g inR d pU pO ent groups first hW hsp hU hO)

end Value

end AtPublicFiles.KeyValueHolds

#print axioms AtPublicFiles.KeyValueHolds.quietHalf_test
#print axioms AtPublicFiles.KeyValueHolds.quietHalf_needs
#print axioms AtPublicFiles.KeyValueHolds.rootedAll_key
#print axioms AtPublicFiles.KeyValueHolds.atPlaces_value
#print axioms AtPublicFiles.KeyValueHolds.atAll_value
#print axioms AtPublicFiles.KeyValueHolds.noStop_value
#print axioms AtPublicFiles.KeyValueHolds.noSecond_value
#print axioms AtPublicFiles.KeyValueHolds.halved_value
#print axioms AtPublicFiles.KeyValueHolds.rooted_value
