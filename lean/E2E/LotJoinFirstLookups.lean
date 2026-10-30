-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotJoinFirstLookups.lean: THE FOUR CELLS AT THE TWO LOOKUPS (members 4 and 10 of the key file's first chain) OF WHAT IS LEFT OF THE JOIN
(`LeftJoin`, E2E/LotJoinFirst.lean), STRUCK UNDER ONE NAMED PREMISE: at the laid thread `joinThread d (laterValue Z d K₀) w x`, by the lookups'
`lookupFiveAtTheKeyAtTheSendersRows` (AtFullSide/Honest/K3/Key/LookupFiveAtTheKeyAtTheSendersRows.lean, over part 5's
AtFullSide/K1/KeyOwnersLayInOrder.lean), with every premise paid that we can pay.

  `find_look0`, `find_look1`: in `keyProver K`'s first list the half found at a lookup's place is the owned seat at K's own letters, where K
    stands at its places.
  `cells_laid`: the stored table's cells spell the index's matrix, at the laid filling: at every row and column.
  `LookupsLeft`: WHAT STAYS: the thread's witness reads the rows that the two owners' senders lay (`WitnessReadsTheSendersRows`: the mask
    tables at the numbers of the takes; the multiplicities' main table at the numbers that the bits read), at every pair of coins that
    are the book's at the two owners' addresses: the lookups' row 20.
  **`lookupsFive`**: `FiveAtBorder` at 4 and 10 at the laid thread, at every Said and every fall, from `LookupsLeft`.
  `LeftSix`: `LeftJoin` less its four cells at 4, 10: five fields, SIX CELLS: ExchangeS at 5, 11 · PlaysS, AcceptedS at 15 · ExchangeS at 16 ·
    (Eval) at 17.
  **`leftJoin_of_six`**: `LeftJoin` at the laid Q from `LeftSix` and `LookupsLeft`.

PAID HERE: the two halves by name (`find_look0`, `find_look1` at `FirstPublic.places`; the value's letters by unfolding; the lookups'
`matrixWeights` is `matrixReader` by unfolding) · inRange: a valid input's matrix is in range (`rel_inRange`, E2E/LotLaterValue.lean) · kind₁ at 4, 10 is
`LookupKeeps` (by unfolding) · `ReadsL` · same: what reads alike is `readH.same` (by unfolding) · cells (`cells_laid`, by `matAt_cells`) · the public three.

Limits. AN IMPLICATION. A member of `LookupsLeft`: lookupsLeft_laid (E2E/LotWitnessReads.lean). All content is the lookups'. `ThrS` in front, the premise inside every debt, is met by
nothing here. In scope, at the written sizes and the written book. Nothing on soundness, completeness, hiding or binding.
-/
import AtFullSide.Honest.K3.Key.LookupFiveAtTheKeyAtTheSendersRows
import E2E.LotLaterValue
import E2E.LotJoinFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open OnBytes (E)
open OnBytes.Slice (readE)
open VerifiableInference.Desc.Key (Xi FirstState)
open Johnson.RunOne.KeyRows1 (plan₁ ReadsL)
open AtPublicFiles.KeyThread (one₀)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver keyProver_first)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub lookPlace msgPlace idxPlace rideMsg)
open AtPublicFiles.KeyValues (lookOf multiplicitiesSending indexMaskSending)
open ProofFile.Honest.K1 (dueR)
open AtPublicFiles.Lookup.Key
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/-! ## 1 The halves by name -/

section
variable {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)

theorem find_look0 (h : K.AtPlaces) :
    (keyProver K).first.find? (fun g => g.place == lookPlace 0) =
      some (K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0) := by
  have e0 : ((K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 0) = false := by
    show (K.idx.P.place == lookPlace 0) = false
    rw [h.idx]
    decide
  have e1 : ((K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 0) = false := by
    show (K.msg.P.place == lookPlace 0) = false
    rw [h.msg]
    decide
  have e2 : ((K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0 :
      Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 0) = true := by
    show (K.look0.place == lookPlace 0) = true
    rw [h.look0]
    decide
  rw [keyProver_first]
  simp only [List.find?_cons, e0, e1, e2]

theorem find_look1 (h : K.AtPlaces) :
    (keyProver K).first.find? (fun g => g.place == lookPlace 1) =
      some (K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1) := by
  have e0 : ((K1.proverSideOfSending K.idx : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 1) = false := by
    show (K.idx.P.place == lookPlace 1) = false
    rw [h.idx]
    decide
  have e1 : ((K1.proverSideOfSending K.msg : Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 1) = false := by
    show (K.msg.P.place == lookPlace 1) = false
    rw [h.msg]
    decide
  have e2 : ((K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0 :
      Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 1) = false := by
    show (K.look0.place == lookPlace 1) = false
    rw [h.look0]
    decide
  have e3 : ((K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1 :
      Placed (In1 W₀ Rc) (In1 W₀ Rc) X).place == lookPlace 1) = true := by
    show (K.look1.place == lookPlace 1) = true
    rw [h.look1]
    decide
  rw [keyProver_first]
  simp only [List.find?_cons, e0, e1, e2, e3]

end

/-! ## 2 The five at 4 and 10 -/

section
variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)
  (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi)

/-- The filling of the laid thread. -/
abbrev laidFill :=
  fillH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀) x

/-- **The stored table's cells spell the index's matrix**, at the laid filling. -/
theorem cells_laid (number : Nat) :
    CellsSpellTheIndexsMatrix (laidFill Z d K₀ x) matrixWeights d.source number := by
  intro w₀ rc y _ c _
  show OnBytes.Slice.toF (VerifiableInference.Desc.Key.matAt (one₀ d.source).lin
    (cellsOf (one₀ d.source).lin (matrixReader w₀)) y c) = (matrixReader w₀).entry y c
  rw [matAt_cells, OnBytes.Slice.toF_ofF]

/-- **WHAT STAYS AT THE TWO LOOKUPS.** A premise's form. A member: lookupsLeft_laid (E2E/LotWitnessReads.lean). -/
def LookupsLeft : Prop :=
  ∀ number, number < 2 → ∀ ownCoins keyCoins,
    OwnIs (keyBook K₀) 0 ⟨msgPlace, 0⟩
      (dueR (multiplicitiesSending (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) matrixWeights d.source).P rideMsg) ownCoins →
    OwnIs (keyBook K₀) 0 ⟨idxPlace, 0⟩
      (dueR (indexMaskSending (W₀ := FullSizeMatrix) (Rc := (protocolAtFiles Z).EncodingRandomness) (X := Unit) d.source).P fun _ => none) keyCoins →
    WitnessReadsTheSendersRows K₀ matrixWeights d.source d.numbers d.later (laidFill Z d K₀ x) w.1 w.2.1 x
      (keyProver (offlineValue (files := Z) d)).first
      (tbH d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader (laterValue Z d K₀)) ()
      number (lookOf d.source d.numbers number).base ownCoins keyCoins

variable {Z d K₀ w x}

/-- **`FiveAtBorder` at 4 and 10 at the laid thread.** -/
theorem lookupsFive (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (left : LookupsLeft Z d K₀ w x)
    (Said : Nat → Coins (keyBook K₀) → Mid (In1 FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) Unit → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [4, 10], FiveAtBorder (joinThread d (laterValue Z d K₀) w x) Said fall b := by
  have hp := (firstPublic_atValue (files := Z) hs scope).places
  have hG : ReadsL (laidFill Z d K₀ x).base.h₁ :=
    Johnson.RunOne.KeyRows1.readsL_h₁ (baseH (one₀ d.source)) fun _ _ _ _ => rfl
  exact lookupFiveAtTheKeyAtTheSendersRows K₀ hK hs scope hG ⟨rfl, rfl⟩ Said fall
    (find_look0 _ hp) (find_look1 _ hp)
    (fun input hv => by
      obtain ⟨rfl, hr⟩ := hv
      exact rel_inRange (Z := Z) (d := d) (K₀ := K₀) hr)
    () left (fun _ _ h => h) (fun number _ => cells_laid Z d K₀ x number)

/-! ## 3 What is left of the join's first chain -/

variable (Z d K₀ w x)

/-- **`LeftJoin` less its four cells at 4 and 10**: six cells. A premise's form. -/
structure LeftSix : Prop where
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (joinThread d (laterValue Z d K₀) w x)
    (joinSaid d (laterValue Z d K₀) w x) b
  playsRanges : PlaysS (joinThread d (laterValue Z d K₀) w x) (joinSaid d (laterValue Z d K₀) w x) 15
  acceptedRanges : AcceptedS (joinThread d (laterValue Z d K₀) w x)
    (joinSaid d (laterValue Z d K₀) w x) (fallsBy [] (keyFileDescription d.source d.numbers d.later).first.blocksInOrder) 15
  pile : ExchangeS (joinThread d (laterValue Z d K₀) w x) (joinSaid d (laterValue Z d K₀) w x) 16
  eval : ∀ blk, (joinThread d (laterValue Z d K₀) w x).bs[17]? = some blk → ∀ k s m E ds y cols s',
    Thr (joinThread d (laterValue Z d K₀) w x) 17 k s m E → drawsFit blk.rounds ds = true →
    (joinThread d (laterValue Z d K₀) w x).Stepped blk k s m E ds y cols s' →
    (joinThread d (laterValue Z d K₀) w x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1)

variable {Z d K₀ w x}

/-- **`LeftJoin` at the laid Q, from the six cells and what stays at the lookups.** -/
theorem leftJoin_of_six (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    (hK : fullPub = some K₀) (look : LookupsLeft Z d K₀ w x)
    (six : LeftSix Z d K₀ w x) : LeftJoin d (laterValue Z d K₀) w x where
  playsK3 := fun b hb => (lookupsFive hs scope hK look _ (fun _ _ _ => none) b hb).plays
  exchangeK3 := fun b hb => (lookupsFive hs scope hK look _ (fun _ _ _ => none) b hb).exchange
  exchangeLayer := six.exchangeLayer
  playsRanges := six.playsRanges
  acceptedRanges := six.acceptedRanges
  pile := six.pile
  eval := six.eval

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.find_look0
#print axioms AtPublicFiles.FirstH.Lots.find_look1
#print axioms AtPublicFiles.FirstH.Lots.cells_laid
#print axioms AtPublicFiles.FirstH.Lots.lookupsFive
#print axioms AtPublicFiles.FirstH.Lots.leftJoin_of_six
