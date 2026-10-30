-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/OkAtt.lean: FOR THE ITEM "totalB": THE SEALED LIBRARY's PROMISE Ok AT AN ATTENTION
SEGMENT, AT THE FILLING OF Honest/K9/TotalFill.lean, FROM SIX NAMED FACTS ON THE STATE IN FRONT OF THE BATCHING. A
statement and its proof over the library's laws; no goal is stated. As Honest/K9/OkLay.lean at a feed-forward segment:
the lemmas BENEATH the library's own payer (`P5J.ok0_att_hd2`, Johnson/P5J/K09AreadyHd2.lean) are joined anew, call
for call as in `P5J.ok0_attC`, `core_att_at`, `ownA_at`, `numOk_att`, `planesAtt_mg`, `keysEnts_mg` and the library's
`LinkJoin.kx_of_table`; where these take the table's condition for a public item, the lemma beneath takes the item's
test's yes, or what the item says.
  **`okFill_att`**   under the library's head `P5J.AtMgA` at the older hash, the opening of the description, and the
      filling's pins at the segment 2 g + 1 (its plan A; the built segment Xl; what `digAt` and `placeAt`, twice,
      answer): AT EVERY STATE s WITH: (hq) s is reached at border 14 (2 g + 1) + 9 over the blocks under `below` (each
      behind the test that every word which it is shown is below the prime) (`Walk.Tied.RchAt`) · (hB) a ledger is
      open and has its sizes · (hpart) K9's lens reads a part · (hL) what the public item "leftOn" of the segment says
      · (h5) the test of the public item "K5.okAt" says yes (`okThereB`) · (hpl) the test of the public item
      "K5.plain" says yes (`plainThereB`): `okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s)`
(hpart) comes with the batching's own yes (the library's `LinkJoin.parts_batch`); the other five stay premises.
On a member: the head is met under four premises on the public files, at D := dpZ Z and r := theProofRun (asDescriptionFiles Z)
alone (the library's `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean); no member of what stands beside it
here is shown. Called by Honest/K9/OkFrontAt.lean.
WHAT IS NOT CLAIMED. The six facts at any state. Nothing on any property.

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
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K9Asks (funs_att posPlan_attention h0_of_head)
open VerifiableInference.Desc.LinkJoin (core_att_front hmS_at digHeard_of_leftOn leftOn_digits_front kxCalls_of_item
  kxDigits_front hU_att k5_of_okThere entsFirst_of_plain entsSecond_of_plain planesAtt_of_plain keysEnts_of_plain pi8)
open VerifiableInference.OnPublicFiles (k3LeftOnItemAt)
open Johnson.Desc.First.Walk.Tied (Reach rchAt_raw)
open _root_.Desc.K14.Law (seatZ secondAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The promise at an attention segment, from six facts on the state in front.** -/
theorem okFill_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan} (hA : Bs.G₀.W.A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (z : ProofFile.InstPub) (s : S)
    (hq : Johnson.Desc.First.Walk.Tied.RchAt
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatZ Zp Np) (secondAt Zp Np) (fun s => s)
        (ProofFile.startS Zp) cF) (14 * (2 * g + 1) + 9) ((z, s), ()))
    (hB : ∃ G', s.fork? = some G' ∧ Sized G') (hpart : (Desc.K9.atS.get? s).isSome = true)
    (hL : k3LeftOnItemAt (P5J.At.X Zp) (2 * g + 1) s)
    (h5 : H2K5.Door.okThereB (P.parCOf A).geo s = true)
    (hpl : H2K5.Door.plainThereB (P.parCOf A).iU3 (P.parCOf A).nW s = true) :
    okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD (fixed9 (phiFill tlD) s) := by
  have C := P5J.closed_at_hd h O (by omega : 2 * g + 1 < 25) e3 hd
  have H := posPlan_attention h.scope h.reads O hg e3
  have h0 := h0_of_head h.toAtMg O (by omega : 2 * g + 1 < 25) e3
  have hp := IM.plan_flat O h.laid.planOk
  have hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * (2 * g + 1) + 9) (z, s) := rchAt_raw hq
  have Co := core_att_front h.scope h.reads O hg e3 ((z, s), ()) hq (ProofFile.k8NU Bs.G₀ Xl) tlD tlD psiAll
    ⟨hpart, hB, C.static, C.dig, C.fits, hp⟩ H
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  obtain ⟨P', hh, -, -, -, L⟩ := leftOn_digits_front h.scope h.reads O hp (by omega : 2 * g + 1 < 24) hr hB 0
  have hD' : placeAt Bs.G₀.W (2 * g + 1) true = some pD := by
    rw [O.W]
    exact hD
  have hU := hU_att h.scope h.reads O hg hA ((z, s), ()) hq pi8 (phiAll tlD psiAll) tlD (fun _ => rfl)
  have hrd := heard5_of_rdAll tlD s
  exact ⟨⟨Co, k5_of_okThere (P.parCOf A) s h5 (phiAll tlD psiAll) rdAll hrd,
      entsFirst_of_plain pi8 (phiAll tlD psiAll) rdAll (P.parCOf A) hpl hrd Co.static hU h0,
      entsSecond_of_plain pi8 (phiAll tlD psiAll) rdAll (P.parCOf A) hpl hrd Co.static hU h0⟩,
    kxAtt_of
      (kxAll3_of ⟨kxCalls_of_item tlD hL pC hC,
          kxDigits_front h.scope h.reads O hp (by omega : 2 * g + 1 < 24) hr hB 0 tlD pD hD'⟩
        ⟨funs_att h.scope h.reads O hg hr tlD psiAll, digHeard_of_leftOn L tlD psiAll,
          hmS_at h.scope h.reads O hx e3 hr C.ms C.fits tlD psiAll⟩)
      ⟨planesAtt_of_plain (phiAll tlD psiAll) hpl Co.static hU h0,
        keysEnts_of_plain (phiAll tlD psiAll) hpl hrd Co.static hU h0⟩⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.okFill_att
