-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/OwnerK.lean: THE HEAD's EXAMPLE: publicOfO AT THE STORED FULL-SIZE FILES: the
columns of the last array that the head reads of its owner. The owner is the plan of the last group
of layers (`Verify.ownerOf`, OnBytes/Model/VerifyPublic.lean). The head's check asks two things of
the owner in a run (OnBytes/Model/Head.lean, "internal-h-owner-TX"): that its list `tl.ix.TX` is not
empty, and that the last entry of its list `tl.kTX` is the border's number of columns; no routine of
the planner asks either. THE SECOND HALF ALONE is shown here, at the stored full-size files: both
numbers are 400. The first half is not stated in this file. A law file; no running text imports it.

Definitions.
  `ownerKB k`: a test in the form of `owners_W` (Johnson/AtFull/Public/Owners.lean): behind
    `Layer.Pub.of` and `plansG`, `ownerOf` returns an owner O with O.tl.kTX.back? = some k. No free
    letter.
Statements.
  `ownerK_W`: ownerKB 400 = true. `ownerK_bent`: ownerKB 401 = false. `ownerK_first`: ownerKB 1536 =
    false: 1536 is the list's other entry, its first (by an evaluation the list is #[1536, 400]): so
    the test reads the last. By evaluations in Lean's kernel (`decide +kernel`).
  `owner_kTX`: at the letters of `publicOfO_zFull_of_rest` (Johnson/AtFull/Public/Join.lean), each
    pinned by «its maker = .ok the letter»: owner.tl.kTX.back? = some 400.
  `border_kxb`: (borderOf yFull).kxb = 400, out of `yFull_border` (Johnson/AtFull/Public/Kit.lean).
  `hK_of_rest`: if the stored layout file has 224975 bytes and publicOfO returns W at the stored
    full-size files: W.owner.tl.kTX.back? = some 400, (borderOf W.y).kxb = 400, and so
    W.owner.tl.kTX.back? = some (borderOf W.y).kxb. The third follows from the first two; it is kept
    as the second clause of what the head's check asks, to the letter.
  `hK_older`: the same at the program `verify-on-bytes`'s `Verify.publicOf`, by `publicOfO_older`
    (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean).

Limits. The full size, at the stored free numbers alone; at the second hash function. The closed
fact stands at the twins of the routines (Johnson/AtFull/Public/Twins.lean), tied by general laws in
their own files. THE ONE PREMISE, hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975, IS NOT PROVED HERE, as in
Join.lean. `ownerReads` (Johnson/AtFull/Head/PlanReads.lean), whose value at this owner is a closed
fact already (`ownerReads_W`, Johnson/AtFull/Public/OwnerCross.lean), does not read `tl.kTX`: so
this fact is no projection of that one. No general law on `kTX` is stated. No example of the head is
shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth. Nothing on soundness.
-/
import Johnson.AtFull.Public.Join
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)
open OnBytes.Road.K4.Trial.Values (PW yFull polLayout_W)
open OnBytes.Road.K4.Trial.AttK7Owners (withPubC onOk)
open OnBytes.Tie.Pv.Plan (scalesF)
open OnBytes.Model.Layer (ropeTable)
open AtFull.Public (open_pubC onOk_ex' yFull_border yFull_p3 publicOfO_zFull_of_rest)

/-- Behind the layers' public numbers and plans the owner's last entry of `kTX` is k. -/
def ownerKB (k : Nat) : Bool :=
  withPubC fun L => onOk (Layer.plansG L) fun G =>
    onOk (Verify.ownerOf L.y G) fun O => decide (O.tl.kTX.back? = some k)

set_option maxHeartbeats 0 in
theorem ownerK_W : ownerKB 400 = true := by decide +kernel

set_option maxHeartbeats 0 in
/-- A bent twin: one column more: rejected. -/
theorem ownerK_bent : ownerKB 401 = false := by decide +kernel

set_option maxHeartbeats 0 in
/-- The list's first entry is another number: the test reads the last. -/
theorem ownerK_first : ownerKB 1536 = false := by decide +kernel

/-- **At the join's own letters.** -/
theorem owner_kTX {sc : Layer.Scales} {wsLay : WsLay} {layers : Layer.Pub}
    {G : Array Layer.HPlan2} {owner : Head.Owner}
    (e3 : Layer.scalesOf yFull.h scalesF.toArray = .ok sc)
    (e4 : wsLayOf (weightShape PW yFull) true PW.lkW = .ok wsLay)
    (e6 : Layer.Pub.of yFull sc (ropeTable 12 500000 128 10) wsLay PW.h.V #[] PW.settings =
      .ok layers)
    (e7 : Layer.plansG layers = .ok G) (e11 : ownerOf yFull G = .ok owner) :
    owner.tl.kTX.back? = some 400 := by
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨-, -, -, p10, -⟩ := Johnson.Unfolds.ledger_tables VerifierAndGoals.inScope_full hR polLayout_W
  have hA := ownerK_W
  unfold ownerKB at hA
  obtain ⟨sc2, ws2, ro2, L2, f3, f4, f5, f6, hA⟩ := open_pubC hA
  rw [yFull_p3] at f4
  obtain rfl : sc = sc2 := Except.ok.inj (e3.symm.trans f3)
  obtain rfl : wsLay = ws2 := Except.ok.inj (e4.symm.trans f4)
  obtain rfl : ropeTable 12 500000 128 10 = ro2 := Except.ok.inj (p10.symm.trans f5)
  obtain rfl : layers = L2 := Except.ok.inj (e6.symm.trans f6)
  have Ly : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  obtain ⟨G2, f7, hA⟩ := onOk_ex' hA
  obtain rfl : G = G2 := Except.ok.inj (e7.symm.trans f7)
  obtain ⟨ow2, f11, hA⟩ := onOk_ex' hA
  rw [Ly] at f11
  obtain rfl : owner = ow2 := Except.ok.inj (e11.symm.trans f11)
  exact of_decide_eq_true hA

/-- The border's number of columns. -/
theorem border_kxb : (borderOf yFull).kxb = 400 := by
  rw [yFull_border]
  rfl

/-- **At what publicOfO returns at the stored full-size files.** -/
theorem hK_of_rest (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {W : Public}
    (hW : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok W) :
    W.owner.tl.kTX.back? = some 400 ∧ (borderOf W.y).kxb = 400 ∧
      W.owner.tl.kTX.back? = some (borderOf W.y).kxb := by
  obtain ⟨sc, wsLay, HLy, l, ps, layers, G, seenA, owner, e3, e4, -, -, -, e6, e7, -, -,
    ⟨e11, -⟩, hX⟩ := publicOfO_zFull_of_rest hsz
  obtain rfl := Except.ok.inj (hX.symm.trans hW)
  have k1 : owner.tl.kTX.back? = some 400 := owner_kTX e3 e4 e6 e7 e11
  have Ly : layers.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have k2 : (borderOf layers.y).kxb = 400 := by
    rw [Ly]
    exact border_kxb
  exact ⟨k1, k2, k1.trans (congrArg some k2.symm)⟩

/-- **The same at `verify-on-bytes`'s own routine.** -/
theorem hK_older (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {W : Public}
    (hW : Verify.publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok W) :
    W.owner.tl.kTX.back? = some 400 ∧ (borderOf W.y).kxb = 400 ∧
      W.owner.tl.kTX.back? = some (borderOf W.y).kxb :=
  hK_of_rest hsz ((publicOfO_older _ _ _).trans hW)

end AtFull.Head

#print axioms AtFull.Head.ownerK_W
#print axioms AtFull.Head.ownerK_bent
#print axioms AtFull.Head.ownerK_first
#print axioms AtFull.Head.owner_kTX
#print axioms AtFull.Head.border_kxb
#print axioms AtFull.Head.hK_of_rest
#print axioms AtFull.Head.hK_older
