-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/LastLine.lean: THE CODE SWITCH's NAMED CONDITION AT THE COMPOSED MEANING's CLOSED
    CONSTANT (`P5J.AtMgA.K2Cond`, Johnson/Goal/Skeleton/Kinds/K2Bridge.lean) FROM THE HEAD, NAMED
        TESTS ON PUBLIC DATA, THE HEAD WITH THE FACTS ON REACHED STATES AND THREE "THE TYPE HAS A
        MEMBER": NO PREMISE IS ASKED AT A PLACE. One theorem. A law file: no sub-protocol
        imports it.

Why. The condition asks, at each of the 25 places of the kind, that there be parameters with the 74
    fields of `K2AllOwes` (Johnson/Top/H0/K2Ties/Assembly.lean). Each field has found a payer at the
    constant's own terms. Here Lean holds that all of them meet: at one
    place, one piece, one door, one choice of the parameters.

What is said. `k2Cond_last`: IT ENDS IN `Hd.K2Cond L₀`.
  THE PARAMETERS AND THE DOOR: `lists_at_const` (Johnson/P1K2R/ListsAtConst.lean)
      hands, at every place of the kind, the sub-protocol, its door with its properties, the written
      rounds, the written table's entry r, the written frame W, and its three lists `T14Left`,
      `T23More`, `T3More`, from the head and five named tests (`K2Tests`).
  35 FIELDS OF `K2Short` (Johnson/P1K2R/Shorter.lean): `t14_fields_const` (26, TiesOneFour.lean),
      `t23_fields_const` (8, TiesTwoThree.lean), `t3_hAt_const` (hAt, TieThreeConst.lean).
  THE OTHER 27 (`K2Rest3`), EACH A CALL: said, hsam, hidx (Johnson/P1K2R/TableAtConst.lean) · w2
      (`T23More`'s) · hrow, hcar, hdoor (CarryAtConst.lean) · hW, hz, ht (RowClosedConst.lean) · hp
      (`P1K2.hp_const`, ListsAtConst.lean) · hpl (`Sits.plan`) · he, hk, hS, leftDoor
      (`lists_at_const`) · hins, hctx, hoP, hoC, hoR (LastJoin3.lean) · hkeys (PieceAtRow.lean) · hd
      (Johnson/Top/H0/K2Ties/AtConstant.lean) · hFk, hHands (HandsConst.lean, by `hHands_at`) · hD
      (Johnson/Top/H0/K2Caller/DoorKeepsMade.lean, at `T23More`'s keepsOut) · O (`k2Owes_at_const`,
      OwesAtConst.lean, ALL FOURTEEN OF ITS FIELDS PAID: left by `left_of_seat`, base by `base_at`
          (LastJoin5.lean), the fence by the premise on `P5J.AtMgR`, headBack and headBears by
      Johnson/Top/H0/K2Ties/HeadAtConst.lean, the test offC by OffHead.lean).
  `spotsFitB Zp`: `H2K12.spots_atAll` (Johnson/Loose/H2K12/SpotsAtAll.lean), under
      the cut.
  ITS PREMISES, WHOLE. (i) The head Hd (what it holds: LastLineHead.lean's limits); L₀'s three lists
      are the description's own. (ii) NAMED TESTS
      ON PUBLIC DATA: `madePinnedAt` · the cut (`cutOf cF.blocksInOrder = cutFirstFull`) · `sendsAreB` ·
      `tableWrittenB` · `linkPlanB` (at the 23) · `k5PlanB` (at 1; at attention's
      segments) · `headPlanB` (the last three stand at the parameters `(dC Hd).pubD`, a
          noncomputable term that names the proof Hd); and
          "25 segments", "the output head's lookup has heard nothing".
          (iii) THE HEAD WITH THE FACTS ON REACHED STATES (`P5J.AtMgR`) at "reached … and no mark",
          at every list L that `P5J.At.laid?` names. (iv) THREE TIMES "THE TYPE HAS A MEMBER": the
          frame's oracle strings; at an entry of the written table, the typed statement behind and
          the typed stage's statement: parameters that the condition binds and whose value no field
          reads (the first and
      the third) or reads as a default (the second).

Limits. THE PREMISES ARE NOT SHOWN TO HOLD TOGETHER: no example: the theorem may be idle. A member
    of the head Hd is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/).
    No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K2R.ListsAtConst
import Johnson.P1K2R.LastJoin5
import Johnson.Top.H0.K2Ties.HeadAtConst
import Johnson.Loose.H2K12.SpotsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb IOR
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Chain Claim FileDescription Strs Wit KindName smpHeld)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Door (Laid snAt sendsAreB laidAtCodes)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers sampledIn sameMembers flatPlacesOf
    laysPads)
open VerifiableInference.Desc.First.K2Hands
open VerifiableInference.Desc.First.K2 (ownPiece MembersLike SmpLike SeedReads)
open VerifiableInference.Desc.First.K2Ties (Wq K2Owes DecBlind Left HeadBears saidBehindB
    decBlind_at AtWritten AtTold at_written at_told sends_at offC_head codes_of_sends left_of_seat)
open VerifiableInference.PlanWritten (cutFirstFull madePinnedAt)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (HandsR openAt)
open P1K2 (EQ pubAt LeftDoor EndsUnmarked BookDoor mOf said_at hsam_at hidx_at k2No_mOf
    k2_written_at_row k2_unmarked_at k2_spots piece_base_trees_at flat_planOk linkPlanB k5PlanB
    headPlanB)
open Johnson.G (smpTop aOfK keptBitsB keptShapeB storedB fxAt)
open _root_.Run (ckP)
open _root_.Tw.K2 (switchNotices)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF
                  : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}


set_option maxHeartbeats 32000000 in
/-- **The named condition**, from the premises that this file's head names whole. -/
theorem k2Cond_last (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) (L₀ : P5J.Free numsFull Dw
                (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
                            = L₀.c₁ :: L₀.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L₀.c₂ :: L₀.k₂) (q₃ :
                                                 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L₀.c₃ :: L₀.k₃) (hy : madePinnedAt Zp.p.X.P
                                                                      Zp.p.chains.made Zp.first Zp.made = true) (hcut : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder
                                                                      = cutFirstFull) (hSB : ∀ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ → sendsAreB
                                                                      Zp.made.proof.1 358 (snAt Zp G₀ IM.placesW) = true) (hTW : tableWrittenB Z.pol Z.lay Z.KL =
                                                                      true) (h25 :
                                                                      Zp.s₀.check.frame.shape.link.length = 25) (hLP : ∀ m, m < 23 → linkPlanB Zp (dC Hd).pubD.nsOf
                                                                      (dC Hd).pubD.d3 (m + 1) = true) (hK1 : k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout 1 = true) (hK5
                                                                      : ∀ m, m < 23 → IM.subW (m + 1) = .attention → k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout (m +
                                                                      1) = true) (hHP : headPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true) (hh : Zp.p.X.H.tl.heard
                                                                      = none) (hR : ∀ L, P5J.At.laid? Zp = some L → P5J.AtMgR OnBytes.secondHashFunction Z Dw r₀ Zp Np cF Hd.rchU
                                                                          Prod.fst L) (hY : Nonempty (frC Dw).E.Str) (hI : ∀ {r : SwRow}, r ∈ tableFullLit → ∀ (h :
                                                                          r.ok = true) (iJ :
                                                                      ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
                                                                      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent) (iQ : ((rowsAt r
                                                                      (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says h)).oM
                                                                      (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent), Nonempty (TB
                                                                      (Letters.plain r (r.ok_says h)) iJ iQ) ∧ Nonempty ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r
                                                                      (r.ok_says h)) iJ iQ).sw).X × (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ
                                                                      iQ).sw).Ex.Str)) :
    Hd.K2Cond L₀ := by
  have Ts : K2Tests Z Zp Np cF := ⟨hy, hcut, fun _ _ _ _ O => hSB _ O.blank, H2K12.spots_atAll Hd
      hcut, h25⟩
  intro k q pl hq ha hk
  obtain ⟨B, enter, leave, d₁, d₂, extq, Bs, bs, A', B', r, W, hok, hB, hS, hLD, hE, hBD, e, he,
      hkk, T, U, V⟩ := lists_at_const Hd L₀ q₁ q₂ q₃ Ts k q pl hq ha hk
  have hi : k < 357 := by
    rcases k2_spots k pl ha hk with ⟨l, _, _, rfl⟩ | rfl | rfl <;> omega
  obtain ⟨y₀⟩ := hY
  obtain ⟨⟨b₀⟩, ⟨d₀⟩⟩ := hI (List.mem_of_getElem? T.row) hok (iJW (r.ok_says hok) T.kA T.fitW) (iQW
      (r.ok_says hok) T.kA T.fitW)
  have hc := row_closed T.row
  have Aw : AtWritten Zp cF := at_written T.scope T.laid T.pinned
  have At' : AtTold Zp cF := at_told T.cut Aw
  have hs := sends_at T.scope T.laid T.pinned
  have hPl := places_at_const Aw hs T.laidL
  have hTW' : tableWrittenB Zp.pol Z.lay Zp.KL = true := by
    rw [(ProofFile.Law.pub_files Hd.toAtMg.laid.pub).1, (ProofFile.Law.pub_files Hd.toAtMg.laid.pub).2]
    exact hTW
  have hp := P1K2.hp_const Hd.toAtMg T.opened hTW Ts.spots h25 k pl ha hk T.row
  have eK := k2No_mOf ha hk
  have eN : noAt (mOf k) = k := eK
  have hds : q.ds = [d₁, d₂] := by rw [e]
  have hBp : B.planOk = true := flat_planOk T.opened Hd.toAtMg.laid.planOk B (List.mem_of_getElem?
      hB)
  have TF := t14_fields_const T hok
  have UF := t23_fields_const T U hok L₀.c₀ d₀
  have VF := t3_hAt_const T V hok B q.base d₁ d₂ L₀.c₀
  rw [eK] at TF UF VF
  have hdoor := hdoor_const (F := (frC Dw)) (dC Hd).N (mgAll (dC Hd) mgBase) Zp T.way
  rw [eN] at hdoor
  have R3 : K2Rest3 (F := (frC Dw)) (dC Hd) Hd.rchU hok (iJW (r.ok_says hok) T.kA T.fitW) (iQW
      (r.ok_says hok) T.kA T.fitW) (seatNew (P5J.At.N Zp cF) (mOf k) r) q.base d₁ d₂ L₀.c₀
      (ProofFile.rowAtK2 Zp.pol Z.lay Zp.KL) (ProofFile.pAtK2 Zp) (doorZ Zp) (mOf k) B enter leave P5J.fullLinks
      P5J.At.ps k (K2.n0At (mOf k + 1)) b₀ ((below B).lift Prod.snd fun t s => (t.1, s)) extq pl
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1) _ (Meaning.K2.FkR Zp cF) :=
    { said := said_at ha hk
      w2 := U.w2
      hrow := hrow_const hTW' T.row
      hW := hc.2.1
      hz := hc.2.2.1
      ht := hc.2.2.2
      hp := hp
      hpl := hS.plan hBp
      he := he
      hk := hkk
      hins := (ins_at ha hk).1
      hctx := (ins_at ha hk).2
      hoP := (outs_at ha hk).1
      hoC := (outs_at ha hk).2.1
      hoR := (outs_at ha hk).2.2
      hsam := hsam_at _ ha hk
      hidx := hidx_at _ ha hk
      hkeys := keysFit_at_row Hd.toAtMg L₀ q₁ q₂ q₃ k q hq hi B hB _ hS.rounds T.firstTree hds _ _ _
          _ _
      hd := decBlind_at Hd
      hFk := fun z a u => Meaning.K2.fk_of_rchAt u.1.1
      hHands := hHands_at Hd hy hcut hSB hLP hK1 hK5 hHP hh ha hk hB _
      hdoor := fun z a ho _ hm t het => hdoor z a ho hm t het
      hcar := hcar_const Hd (mOf k)
      hS := hS
      leftDoor := hLD
      hD := hD_of_keepsOut _ _ _ _ _ U.keepsOut _ b₀
      O := fun z => k2Owes_at_const Hd ha hk z _ Aw At' hs (hR _ T.laidL) hPl (offC_head Hd.toAtMg
          hy) (left_of_seat (W := Wq
          numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok) (⟨below (K2.codeSwitchKind (ProofFile.pAtK2 Zp (mOf k))),
          q.base, [d₁, d₂], [], fun _ _ w => w, (k2ErrAt (F := (frC Dw)) hok (iJW (r.ok_says hok)
          T.kA T.fitW) (iQW (r.ok_says hok) T.kA T.fitW) (dC Hd).G (seatNew (P5J.At.N Zp cF) (mOf k)
          r) q.base d₁ d₂ (ProofFile.pAtK2 Zp) (mOf k))⟩ : Piece (ckP .two) (frC Dw) Rec Unit (Wq
                numsFull.rows (P5J.colsAt numsFull) P5J.At.Tok)) _ rfl rfl B enter leave hS.rounds hS.step
          hLD.1 hLD.2 (extW (F := (frC Dw)) (dC Hd) d₁ d₂ L₀.c₀ P5J.fullLinks pl z)) (base_at Hd L₀
          q₁ q₂ q₃ hq ha hk hB hS.rounds) (K2Ties.headBack_at Hd z) (K2Ties.headBears_at Hd Aw pl
          (k2_link_lt ha hk)) }
  exact ⟨Unit, Unit, _, r, hok, _, _, _, _, _, _, _, _, _, _, _, _, d₀, y₀, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e, rfl, k2_unmarked_at _ B enter leave
      hS hLD hE _ _ d₁ d₂ extq, k2AllOwes_of_short (k2Short_of_t14_t23_t3 TF UF VF R3)⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Cond_last
