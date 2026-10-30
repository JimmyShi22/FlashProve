-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/ClosingPlainAndStart.lean: two premises that the law on the verdict at the public files takes beside the invariants
(`yesZ_of_base_threadsJ`, E2E/CompleteAsIOPByBase.lean), at the letters of AtFullSide/Honest/TheOneObject.lean: the base prover A.H, read
through the table's coins, and the sides that completeness is stated with.

  Q : `PlainAt` (E2E/BridgeJoinAtFiles.lean): six clauses on the description and the rows' prover: the sealing round is plain; a side stands
      wherever an item is declared, and wherever a root is sent; no round asks for more non-zero elements than elements; every stored
      table has the encoder's width; `ready` returns once
  h₀ : the description's first test accepts one written instance

  `closingPlain_of_one`            Q from its last clause alone: the other five need the head and the maker's return, no more
  **`closingPlain_of_theOneObject`**   Q from a value of the object: `ready` returns at a served request, which is tied
  **`closingStart_of_theOneObject`**   h₀ from a value of the object, at any public files under the head: the instance is a served request's,
                                   written with its own out-of-domain sample
  **`closingStart_at_named`**          h₀ at the two named sets of files, from the head alone

By: `sides_are_whole` (Johnson/Desc/ProofFile/Honest/K1/Pay/Whole.lean); `halvedAll_rows`, `rootedAll_rows` (Honest/ThruRowsMore.lean);
`ready_rows_thru` (Honest/ThruRows.lean); `nonZero_atFiles` (E2E/BridgeNonZero.lean); `width_atFiles` (E2E/RoadPublicRows.lean);
`crossing_rows`, `crossing_range` (AtFullSide/Honest/CrossingPremises.lean); `key_of_atPure` (Honest/ThruAtPure.lean);
`TheOneObject.readyReturns`, `every_served_request_is_tied` (AtFullSide/Honest/TheOneObject.lean); `servedRequest_met`
(E2E/CompleteAsIOPServedLaws.lean); `okStart_at_named` (E2E/FirstBegun.lean).

Limits. Implications: no value of the object is made here. The table's randomness, the out-of-domain seed and the prover's coin at which
`ready` is shown to return are letters: one value of each is asked. The tests on the sides read places and declared rounds alone. The head
and the return of the maker are premises. No property is claimed.
-/
import AtFullSide.Honest.CrossingPremises
import Johnson.Desc.ProofFile.Honest.K1.Pay.Whole
import E2E.RoadPublicRows
import E2E.BridgeNonZero
import E2E.FirstBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles readFiles InScope)
open LPFD.Full (instanceAsPlainRecord)
open FlashProve (committerCoinCountLessOne)

local instance (priority := high) nonemptyPadZ_closingPlainAndStart : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyRunValue_closingPlainAndStart : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_closingPlainAndStart : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The six clauses from the last one**: the other five from the head and the maker's return. -/
theorem closingPlain_of_one (h : HeadAtReturn Z A)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (one : ∃ w₀ rc x k R, ProofFile.Honest.ready (descZ (onlineReturn Z A).Z h.places h.firstChain)
      (onlineReturn Z A).B
      (provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
        (A.H.thru id (tableCoins Z) matrixInput.dummy)) w₀ rc x k = .ok R) :
    PlainAt Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
      (A.H.thru id (tableCoins Z) matrixInput.dummy) := by
  obtain ⟨hh, hrt, hs⟩ := ProofFile.Honest.K1.Pay.sides_are_whole (I := matrixInput)
    (S := OnBytes.HonestTrace.Sz.ref) (O := openHonest) rfl h.head made
  have e : A.F = h.description := (atPure_at_laid h.head.laid made).2
  rw [e] at hh hrt hs
  exact ⟨hs,
    (halvedAll_rows id (tableCoins Z) matrixInput.dummy (theSides h) (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H
      (crossing_rows h) (key_of_atPure made).symm).trans hh,
    (rootedAll_rows id (tableCoins Z) matrixInput.dummy (theSides h) (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H
      (crossing_rows h) (key_of_atPure made).symm).trans hrt,
    nonZero_atFiles Z _ _ _ h.head.scope h.head.laid, width_atFiles Z _ _ _ h.head.scope h.head.laid, one⟩

variable {h : HeadAtReturn Z A} {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- **The six clauses, from a value of the object.** -/
theorem closingPlain_of_theOneObject
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : TheOneObject h hr)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) :
    PlainAt Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
      (A.H.thru id (tableCoins Z) matrixInput.dummy) := by
  obtain ⟨i, x', hx⟩ := servedRequest_met committerCoinCountLessOne Z h.head.scope hr
  have ht := every_served_request_is_tied (h := h) (hr := hr) h.head.scope 0 i r e x' hx
  obtain ⟨R, hR⟩ := O.toTheThreadsHalf.readyReturns made 0 (i, r, e) _ c ht
  refine closingPlain_of_one h made
    ⟨i, r, instanceAsPlainRecord (x', (protocolAtFiles Z).recOf i r e), pursesOf c, Ready.thru id (tableCoins Z) i r R, ?_⟩
  have hR' : ProofFile.Honest.ready (descZ (onlineReturn Z A).Z h.places h.firstChain) (onlineReturn Z A).B A.H (id i)
      (tableCoins Z r) (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf i r e)) (pursesOf c) = .ok R := hR
  have e2 := ready_rows_thru id (tableCoins Z) matrixInput.dummy (theSides h) (cmAlong (AZ Z) PadZ (holdZ Z)) 0 A.H i r
    (instanceAsPlainRecord (x', (protocolAtFiles Z).recOf i r e)) (pursesOf c) (crossing_range made) (crossing_rows h) (key_of_atPure made).symm
  rw [hR'] at e2
  exact e2

/-- **The first test accepts one written instance, from a value of the object.** -/
theorem closingStart_of_theOneObject
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : TheOneObject h hr)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) :
    ∃ z₀, (descZ (onlineReturn Z A).Z h.places h.firstChain).okStart (instanceAsPlainRecord z₀) = true := by
  obtain ⟨i, x', hx⟩ := servedRequest_met committerCoinCountLessOne Z h.head.scope hr
  have ht := every_served_request_is_tied (h := h) (hr := hr) h.head.scope 0 i r e x' hx
  obtain ⟨R, hR⟩ := O.toTheThreadsHalf.readyReturns made 0 (i, r, e) _ c ht
  exact ⟨(x', (protocolAtFiles Z).recOf i r e), O.startFit ⟨0, (i, r, e), _, c, R, ht, hR⟩⟩

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The first test accepts one written instance, at the two named sets of files.** -/
theorem closingStart_at_named (h : HeadAtReturn Z A) (hZ : VerifierAndGoals.NamedFiles Z) :
    ∃ z₀, (descZ (onlineReturn Z A).Z h.places h.firstChain).okStart (instanceAsPlainRecord z₀) = true :=
  ⟨(FlashProve.dataAtFiles FlashProve.flashProveData Z).G.z₀, AtPublicFiles.Start.okStart_at_named hZ h.head.laid _⟩

end AtFullSide.Honest

#print axioms AtFullSide.Honest.closingPlain_of_one
#print axioms AtFullSide.Honest.closingPlain_of_theOneObject
#print axioms AtFullSide.Honest.closingStart_of_theOneObject
#print axioms AtFullSide.Honest.closingStart_at_named
