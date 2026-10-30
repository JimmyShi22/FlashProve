-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OkHead.lean: FOR THE ITEM "totalB": THE SEALED LIBRARY's PROMISE Ok AT THE HEAD's
SEGMENT, AT THE FILLING OF Honest/K9/TotalFill.lean, FROM FOUR NAMED FACTS ON THE STATE IN FRONT OF THE BATCHING. A
statement and its proof over the library's laws; no goal is stated. As Honest/K9/OkLay.lean and OkAtt.lean: the lemmas
BENEATH the library's own payer (`P5J.ok0_head_hd2`, Johnson/P5J/K09AreadyHd2.lean) are joined anew, call for call as
in `P5J.ok0_head_hd`, `ok0_headC`, `core_head_at`, `ownH_at`, `numOk_head`, `planesHead_mg` and the library's
`LinkJoin.kx_of_table`, but that where these take the table's condition for the public item "leftOn", what the item
says is taken.
  **`okFill_head`**   under the library's head `P5J.AtMgA` at the older hash, the opening of the description, and the
      filling's pins at the segment 24 (the built segment Xl; what `digAt` and `placeAt`, twice, answer): AT EVERY
      STATE s WITH: (hq) s is reached at border 347 over the blocks under `below` (each behind the test that every
      word which it is shown is below the prime) (`Walk.Tied.RchAt`) · (hB) a ledger is open and has its sizes ·
      (hpart) K9's lens reads a part · (hL) what the public item "leftOn" of the segment says: `okFillHead Bs.G₀.W
      (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s)`
(hpart) comes with the batching's own yes (the library's `LinkJoin.parts_batch`); the other three stay premises.
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it
here is shown. Called by Honest/K9/OkFrontAt.lean.
WHAT IS NOT CLAIMED. The four facts at any state. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFill
import Johnson.P5J.K09AreadyHd2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9Asks (funs_head posPlan_head h0_of_head)
open VerifiableInference.Desc.LinkJoin (core_head_front hmS_at digHeard_of_leftOn leftOn_digits_head kxCalls_of_item
  kxDigits_head ledgerB_of_sized merge_clause_347 entsMerge_at_347 entsK6_at_347 entsJoin_at_347' k6_at_347
  join_of_leftOn planesHead_at_347 pi8)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The promise at the head's segment, from four facts on the state in front.** -/
theorem okFill_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (z : ProofFile.InstPub) (s : S)
    (hq : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatZ Zp Np) (secondAt Zp Np) (fun s => s)
        (ProofFile.startS Zp) cF) 347 ((z, s), ()))
    (hB : ∃ G', s.fork? = some G' ∧ Sized G') (hpart : (Desc.K9.atS.get? s).isSome = true)
    (hL : k3LeftOnItemAt (P5J.At.X Zp) 24 s) :
    okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s) := by
  have C := P5J.closed_at_hd h O (by decide : 24 < 25) e3 hd
  have H := posPlan_head h.scope h.reads O e3
  have h0 := h0_of_head h.toAtMg O (by decide : 24 < 25) e3
  have hi := P5J.reads_at_hd O
  have hok := Kinds.Head.Law.InScope.ok_in_scope h.scope h.reads O.public (workOf Bs.G₀.W)
  have hp := IM.plan_flat O h.laid.planOk
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 347 (z, s) := rchAt_raw hq
  have Co := core_head_front h.scope h.reads O e3 ((z, s), ()) hq (ProofFile.k8NU Bs.G₀ Xl) tlD tlD psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches := by decide
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_head h.scope h.reads O hp hr hB 0
  have hD' : placeAt Bs.G₀.W 24 true = some pD := by
    rw [O.W]
    exact hD
  have hL0 := hL
  obtain ⟨pl, -, ⟨hCs, -, LC⟩, -⟩ := hL0
  have k6 := k6_at_347 h.scope h.reads O h.laid.planOk (phiAll tlD psiAll) kapAll (hkap_all tlD) ((z, s), ()) hq
  have jn := join_of_leftOn (phiAll tlD psiAll) kapAll (hkap_all tlD) LC
  exact ⟨⟨Co, k6, jn, merge_clause_347 h.scope h.reads O (a := (z, s)) hr (ledgerB_of_sized hB) tlD psiAll,
      fun name _ => entsK6_at_347 pi8 (phiAll tlD psiAll) tlD _ _ _ kapAll h.scope h.reads O hi e3 H ((z, s), ()) hq
        (fun _ => rfl) (hkap_all tlD) h0 Co.there Co.static hok rfl k6 name,
      entsJoin_at_347' pi8 (phiAll tlD psiAll) tlD _ _ _ kapAll h.scope h.reads O hi e3 H ((z, s), ()) hq
        (fun _ => rfl) (hkap_all tlD) h0 Co.there Co.static hok rfl k6 LC,
      entsMerge_at_347 h.scope h.reads O hr pi8 (phiAll tlD psiAll) (ProofFile.k8NU Bs.G₀ Xl)⟩,
    kxHead_of
      (kxAll3_of ⟨kxCalls_of_item tlD hL pC hC, kxDigits_head h.scope h.reads O hp hr hB 0 tlD pD hD'⟩
        ⟨funs_head h.scope h.reads O hr tlD psiAll, digHeard_of_leftOn L tlD psiAll,
          hmS_at h.scope h.reads O hx e3 hr C.ms C.fits tlD psiAll⟩)
      ⟨planesHead_at_347 h.scope h.reads O hi e3 H ((z, s), ()) hq tlD h0 Co.static⟩⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.okFill_head
