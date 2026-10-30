-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Public/Join.lean: THE HEAD's EXAMPLE: THE DISCHARGE OF publicOfO's LEDGER AT
THE
STORED FULL-SIZE FILES.
  publicOfO_zFull_of_rest   IF the stored layout file has 224975 bytes, THEN publicOfO, at the
  format's
      second hash function, returns at the stored full-size files VerifierAndGoals.storedPublicFiles: at the scan's
      written value PW, the closed plan HW of the model's head (its ledger trimmed), and what its
      own makers return at the layers' layout yFull.
THE ONE PREMISE, RAW: hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975. IT IS NOT PROVED HERE. Asked of Lean's
kernel outright it is not borne (the stack of Lean's thread runs out). It is shown as
Johnson.Unfolds.Layout.lay_size (lean/AtFullSide/Layout/Size.lean), behind a tie of the layout file
that wants a larger thread stack: so this file stays an ordinary one and the last discharge pays.
UNTIL IT IS PAID THIS IS NO RETURN OF publicOfO AND NO EXAMPLE OF ANYTHING.
A JOIN: it calls the ledger publicOfO_of_parts (Ledger.lean) and pays its twenty-two premises:
  h3 · h4 · p4 · p5 · p10 · p11 · the table inside p14   Johnson/Unfolds/LedgerTables.lean
  p7           Johnson/Unfolds/SizesFull.lean (hPar_zFull_of_lay), from hsz
  p1           Values.lean (polLayout_W)
  p2 · p3 · p6 Scales.lean (scales_written · fileWords_zFull) with Values.lean's h_W | dq_W
  p8 · p8'     Small.lean (widths_W · vocabulary_W)
  p9 · p15 – p18   Owners.lean (owners_W, one closed fact, opened by Kit.lean's open_pubC)
  p13 · p19    Johnson/AtFull/Head/ (layout_returns · planH2_returns)
  p14          AttAtW.lean (config_returns)
  p19's premise on the owner · p20   OwnerCross.lean (ownerReads_W · cross_W)
THE LETTERS UNDER «THERE IS»: nine, each pinned by «its maker = .ok the letter». ps is pinned by the
twin groupS at the written table of exponentials. WHAT IS SAID OF X AS A VALUE: P · H · the head's
layout part by part (LaidW) · the attention's twelve arms and views. layers · G · owner are «what
the
maker returns»; the three digests stay terms.
LIMITS. The full size, at the stored free numbers alone. At the second hash function. The closed
facts that it calls stand at twins of the routines, tied by general laws in their own files. No
example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth. No soundness is claimed.
-/
import Johnson.AtFull.Public.Kit
import Johnson.AtFull.Public.AttAtW
import Johnson.AtFull.Public.Scales
import Johnson.AtFull.Public.OwnerCross
import Johnson.AtFull.Head.LayoutAtFull
import Johnson.Unfolds.SizesFull
import Johnson.Road.HeadL5Grp

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtFull.Public
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO callsDigestO tailView)
open OnBytes.Road.K4.Trial.Values (PW hW yBase yFull polLayout_W noFill_W noAsk_W planeCols_W h_W
  ok_unit)
open OnBytes.Road.K4.Trial.AttK7Owners (ttR ownersB armAW)
open OnBytes.Road.K4.Trial.AttL2 (AOf seenGOf mqOf)
open OnBytes.Tie.Pv.Plan (scalesF)
open OnBytes.Model.Layer (ropeTable)

set_option maxHeartbeats 4000000 in
/-- **IF the stored layout file has 224975 bytes, THEN publicOfO returns at the stored full-size
files**, at PW, HW trimmed and what its own makers return. The premise is not proved here. -/
theorem publicOfO_zFull_of_rest (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ (sc : Layer.Scales) (wsLay : WsLay) (HLy : Head.HL) (l : List Attention.Line)
      (ps : List Attention.Plan) (layers : Layer.Pub) (G : Array Layer.HPlan2)
      (seenA : Array SubPlan) (owner : Head.Owner),
      Layer.scalesOf yFull.h scalesF.toArray = .ok sc ∧
      wsLayOf (weightShape PW yFull) true PW.lkW = .ok wsLay ∧
      (Head.layout (headShape PW yFull) yFull.tauFC = .ok HLy ∧
        AtFull.Head.headReads HLy = AtFull.Head.headReadsW ∧
        AtFull.Head.LaidW (Head.layout (headShape PW yFull) yFull.tauFC)) ∧
      Attention.readLines PW.polCallsA = .ok l ∧
      ((List.range 12).mapM (Attention.groupS ttR PW yFull sc (mqOf yFull) l) = .ok ps ∧
        ps.length = 12) ∧
      Layer.Pub.of yFull sc (ropeTable 12 500000 128 10) wsLay PW.h.V #[] PW.settings = .ok layers ∧
      Layer.plansG layers = .ok G ∧
      attentionOwners true 12 (seenGOf G)
        (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩) = .ok seenA ∧
      ((AOf ps.toArray seenA).size = 12 ∧ ∀ x ∈ (AOf ps.toArray seenA).toList.zipIdx,
        (forestSize x.1.fs, x.1.own, smallSize x.1.seam.tl) = armAW ∧
          some (tailView x.1.seam.tl) = Johnson.G.xShapeFull.1.getD (2 * x.2 + 1) none) ∧
      (ownerOf yFull G = .ok owner ∧
        AtFull.Head.ownerReads owner = AtFull.Head.ownerW.reads) ∧
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok
        { P := PW,
          digests := { hCalls := callsDigestO OnBytes.secondHashFunction "call" yFull.calls.toList,
                       hCallsA := VerifiableInference.PlanWritten.Attention.callsDigestO
                         OnBytes.secondHashFunction l,
                       hCallsH := callsDigestO OnBytes.secondHashFunction "callH" HLy.calls.toList },
          layers := layers, hS := headShape PW yFull, HLy := HLy, G := G,
          A := AOf ps.toArray seenA,
          H := { AtFull.Head.HW with Fp := AtFull.Head.HW.Fp.trimL }, owner := owner } := by
  have p1 := polLayout_W
  have hZ := VerifierAndGoals.inScope_full
  obtain ⟨pp, hR, -⟩ := VerifierAndGoals.filesRead.full.2
  obtain ⟨h3, p4, p5, p10, p11⟩ := Johnson.Unfolds.ledger_tables hZ hR p1
  have h4 := yFull_p4
  have hT := Johnson.Unfolds.ledger_exp hZ hR p1
  obtain ⟨hp, p7⟩ := Johnson.Unfolds.hPar_zFull_of_lay hsz
  have hN' := yFull_NGr
  have hh := h_W
  -- the owners' closed fact, opened
  obtain ⟨sc, wsLay, rope, L, e3, e4, e5, e6, hO⟩ :=
    open_pubC OnBytes.Road.K4.Trial.AttK7Owners.owners_W
  obtain rfl : ropeTable 12 500000 128 10 = rope := Except.ok.inj (p10.symm.trans e5)
  have Ly : L.y = yFull := OnBytes.Road.Hd.pubOf_y e6
  have Lsc : L.sc = sc := OnBytes.Road.Hd.pubOf_sc e6
  obtain ⟨G, e7, hO⟩ := onOk_ex' hO
  obtain ⟨l, e8, hO⟩ := onOk_ex' hO
  obtain ⟨ps, e9, hO2⟩ := onOk_ex' hO
  rw [Ly, Lsc, hN'] at e9
  unfold ownersB at hO2
  obtain ⟨seenA, e10, hO2⟩ := onOk_ex' hO2
  dsimp only at hO2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hO2
  obtain ⟨⟨a12, aAll⟩, hown⟩ := hO2
  obtain ⟨owner, e11, -⟩ := onOk_ex' hown
  rw [Ly] at e10 e11
  rw [h4, hN'] at e10
  -- the scales
  have e3' : Layer.scalesOf hW scalesF.toArray = .ok sc := by
    rw [← hh]
    exact e3
  obtain ⟨s, t1, t2, t3⟩ := OnBytes.Road.K4.Trial.AttJ1.scales_written
  obtain rfl : s = sc := Except.ok.inj (t1.symm.trans e3')
  have p2 : Layer.scalesOf yFull.h (fileWords VerifierAndGoals.storedPublicFiles.KL) = .ok s := by
    rw [OnBytes.Road.K4.Trial.AttA5ScalesTie.fileWords_zFull]
    exact e3
  have p3 : Layer.scalesHeld yFull.h s = .ok () := by
    show Layer.scalesHeld yBase.h s = .ok ()
    rw [hh]
    exact t2
  have p6 : Layer.noWrap yFull.h s yFull.dq = .ok () := by
    rw [yFull_dq]
    show Layer.noWrap yBase.h s 5120 = .ok ()
    rw [hh]
    exact t3
  have p8 : Layer.weightWidthsHeld yFull.h yFull.kinds = .ok () := by
    show Layer.weightWidthsHeld yBase.h yBase.kinds = .ok ()
    exact ok_unit (at_yBase OnBytes.Road.K4.Trial.Small.widths_W)
  have p8' : Head.vocabulary (headShape PW yFull) = .ok () := by
    show Head.vocabulary (headShape PW yBase) = .ok ()
    exact ok_unit (at_yBase OnBytes.Road.K4.Trial.Small.vocabulary_W)
  -- the model's head
  obtain ⟨HLy, p13, hL⟩ := AtFull.Head.layout_returns yFull_lPd yFull_tauFC
  -- the attention
  obtain ⟨l', ps', c1, c2, c12, -, p14⟩ := OnBytes.Road.K4.Trial.AttAtW.config_returns
    OnBytes.secondHashFunction noFill_W noAsk_W planeCols_W e3' hT
  obtain rfl : l = l' := Except.ok.inj (e8.symm.trans c1)
  obtain rfl : ps = ps' := Except.ok.inj (e9.symm.trans c2)
  -- the owner's reads
  have hA := OnBytes.Road.K4.Trial.AttK7Owners.ownerReads_W
  unfold OnBytes.Road.K4.Trial.AttK7Owners.ownerB at hA
  obtain ⟨sc2, ws2, ro2, L2, f3, f4, f5, f6, hA⟩ := open_pubC hA
  obtain rfl : s = sc2 := Except.ok.inj (e3.symm.trans f3)
  obtain rfl : wsLay = ws2 := Except.ok.inj (e4.symm.trans f4)
  obtain rfl : ropeTable 12 500000 128 10 = ro2 := Except.ok.inj (e5.symm.trans f5)
  obtain rfl : L = L2 := Except.ok.inj (e6.symm.trans f6)
  obtain ⟨G2, f7, hA⟩ := onOk_ex' hA
  obtain rfl : G = G2 := Except.ok.inj (e7.symm.trans f7)
  obtain ⟨ow2, f11, hA⟩ := onOk_ex' hA
  rw [Ly] at f11
  obtain rfl : owner = ow2 := Except.ok.inj (e11.symm.trans f11)
  have hOw := OnBytes.Road.K4.Trial.AttK7Owners.sameReads_of hA
  have p19 := AtFull.Head.planH2_returns yFull_lPd yFull_border hN' hL hOw
  -- the plans against each other
  have hB := OnBytes.Road.K4.Trial.AttK7Owners.cross_W
  unfold OnBytes.Road.K4.Trial.AttK7Owners.crossB at hB
  obtain ⟨sc3, ws3, ro3, L3, g3, g4, g5, g6, hB⟩ := open_pubC hB
  obtain rfl : s = sc3 := Except.ok.inj (e3.symm.trans g3)
  obtain rfl : wsLay = ws3 := Except.ok.inj (e4.symm.trans g4)
  obtain rfl : ropeTable 12 500000 128 10 = ro3 := Except.ok.inj (e5.symm.trans g5)
  obtain rfl : L = L3 := Except.ok.inj (e6.symm.trans g6)
  obtain ⟨G3, g7, hB⟩ := onOk_ex' hB
  obtain rfl : G = G3 := Except.ok.inj (e7.symm.trans g7)
  obtain ⟨l3, g8, hB⟩ := onOk_ex' hB
  obtain rfl : l = l3 := Except.ok.inj (e8.symm.trans g8)
  obtain ⟨ps3, g9, hB⟩ := onOk_ex' hB
  rw [Ly, Lsc, hN'] at g9
  obtain rfl : ps = ps3 := Except.ok.inj (e9.symm.trans g9)
  obtain ⟨se3, g10, hB⟩ := onOk_ex' hB
  rw [Ly, h4, hN'] at g10
  obtain rfl : seenA = se3 := Except.ok.inj (e10.symm.trans g10)
  rw [Ly] at hB
  have p20 := ok_unit hB
  have e4' := e4
  rw [h3] at e4'
  refine ⟨s, wsLay, HLy, l, ps, L, G, seenA, owner, e3, e4',
    ⟨p13, hL, AtFull.Head.layout_whole yFull_lPd yFull_tauFC⟩, e8, ⟨e9, c12⟩, e6, e7, e10,
    ⟨a12, aAll⟩, ⟨e11, hOw⟩, ?_⟩
  have p17 : attentionOwners yFull.h.p4 yFull.NGr (seenGOf G)
      (ps.toArray.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩) = .ok seenA := by
    rw [h4, hN']
    exact e10
  have key := OnBytes.Road.K4.Trial.AttL2.publicOfO_of_parts (H := AtFull.Head.HW) h3 h4 p1 p2 p3 p4
    p5 p6 p7 p8 p8' e4 p10 p11 p13 p14 e6 e7 p17 e11 p19 p20
  exact key

end AtFull.Public

#print axioms AtFull.Public.publicOfO_zFull_of_rest
