-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OkLay.lean: FOR THE ITEM "totalB": THE SEALED LIBRARY's PROMISE Ok AT A FEED-FORWARD
SEGMENT, AT THE FILLING OF Honest/K9/TotalFill.lean, FROM FOUR NAMED FACTS ON THE STATE IN FRONT OF THE BATCHING. A
statement and its proof over the library's laws; no goal is stated. WHY. The library pays this promise
(`P5J.ok0_layers_hd`, Johnson/P5J/K09AreadyHd.lean) under its table's whole condition in front of the batching, which
holds clauses on the oracles' strings that the honest side's thread does not give. The lemmas BENEATH that payer spend
less. Here they are joined anew, call for call as in `P5J.ok0_layersC`, `core_layers_at`, `ownL_at`, `numOk_layers`
and the library's `LinkJoin.kx_of_table`, but that where these take the table's condition for the public item
"leftOn", the lemma beneath (`kxCalls_of_item`) takes what the item says.
  **`okFill_lay`**   under the library's head `P5J.AtMgA` at the older hash, the opening of the description, and the
      filling's pins at the segment 2 g (the built segment Xl; what `digAt`, `LPFK9.k4ParAt` and `placeAt`, twice,
      answer): AT EVERY STATE s WITH: (hq) s is reached at border 28 g + 9 over the blocks under `below` (each behind
      the test that every word which it is shown is below the prime) (`Walk.Tied.RchAt`) · (hB) a ledger is open and
      has its sizes · (hpart) K9's lens reads a part · (hL) what the public item "leftOn" of the segment says
      (`k3LeftOnItemAt`): `okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s)`
SO `OkFront` (Honest/K9/TotalFront.lean) at a feed-forward segment comes down to these four at the state in front:
(hpart) comes with the batching's own yes (the library's `LinkJoin.parts_batch`,
Johnson/Desc/First/Link/Law/LettersAt.lean); the other three stay premises. On a member: the head is met under four
premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z) alone (the library's
`P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it here is shown.
Called by Honest/K9/OkFrontAt.lean.
WHAT IS NOT CLAIMED. The four facts at any state. The like at an attention segment or the head's. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFill
import Johnson.P5J.K09AreadyHd

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
open VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9Asks (funs_layers posPlan_layers h0_of_head)
open VerifiableInference.Desc.LinkJoin (core_layers_front hmS_at digHeard_of_leftOn leftOn_digits_front okFront_at
  okBack_at entsFront_at entsBack_at kxCalls_of_item kxDigits_front)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The promise at a feed-forward segment, from four facts on the state in front.** -/
theorem okFill_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD))
    {p4 : OnBytes.Desc.First.K4.Par} (hk : LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (z : ProofFile.InstPub) (s : S)
    (hq : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatZ Zp Np) (secondAt Zp Np) (fun s => s)
        (ProofFile.startS Zp) cF) (28 * g + 9) ((z, s), ()))
    (hB : ∃ G', s.fork? = some G' ∧ Sized G') (hpart : (Desc.K9.atS.get? s).isSome = true)
    (hL : k3LeftOnItemAt (P5J.At.X Zp) (2 * g) s) :
    okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s) := by
  obtain ⟨hP, hgp, -⟩ := P1K9.k4Par_of_open h.scope h.reads O g hg p4 hk
  have C := P5J.closed_at_hd h O (by omega : 2 * g < 25) e3 hd
  have H := posPlan_layers h.scope h.reads O hg e3
  have h0 := h0_of_head h.toAtMg O (by omega : 2 * g < 25) e3
  have hp := IM.plan_flat O h.laid.planOk
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (28 * g + 9) (z, s) := rchAt_raw hq
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g) + 9) (z, s) := by
    rw [show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
    exact hr
  have Co := core_layers_front h.scope h.reads O hg e3 ((z, s), ()) hq (ProofFile.k8NU Bs.G₀ Xl) tlD tlD psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_front h.scope h.reads O hp (by omega : 2 * g < 24) hr' hB 0
  have hD' : placeAt Bs.G₀.W (2 * g) true = some pD := by
    rw [O.W]
    exact hD
  exact ⟨⟨Co, okFront_at h.scope h.reads O hp hg hr hB tlD psiAll p4 hP hgp,
      okBack_at h.scope h.reads O hp hg hr hB tlD psiAll,
      entsFront_at h.scope h.reads O hp hg ((z, s), ()) hq hB tlD psiAll h0 Co.static p4,
      entsBack_at h.scope h.reads O hp hg ((z, s), ()) hq hB tlD psiAll h0 Co.static⟩,
    kxAll3_of ⟨kxCalls_of_item tlD hL pC hC,
        kxDigits_front h.scope h.reads O hp (by omega : 2 * g < 24) hr' hB 0 tlD pD hD'⟩
      ⟨funs_layers h.scope h.reads O hg hr tlD psiAll, digHeard_of_leftOn L tlD psiAll,
        hmS_at h.scope h.reads O hx e3 hr' C.ms C.fits tlD psiAll⟩⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.okFill_lay
