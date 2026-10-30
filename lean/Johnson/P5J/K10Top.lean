-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Top.lean: AT THE CLOSED CONSTANT: THE FIELD OF THE KIND K10 (`h.Kind L .K10`) FROM
THE HEAD, `rowsRead Z`, THE FIFTH TIE (reads) AND ONE DEBT: `AtMgA.K10CarAll`: what stands behind
the closing, at all 25 links. A definition, two statements and their proofs: calls.

  `AtMgA.K10CarAll h L`: WHAT IS LEFT OF K10's OWN DEBT. At link 0, and at every link l with 1 ≤ l <
    25: there is a word mW for the fresh mask such that at every sub-protocol b, plan's Q and base
    with the debt's own nine hypotheses `K10Car` holds
    (Johnson/Desc/First/Close/Law/K10LastTwo.lean: the field hCar of `K10Heavy`) AT THE TERMS THAT
    THE JOIN HAS CHOSEN: the link's list, group, flags, seats and numbers (link 0: the five-list) ·
    B, num, pS as in K10ExistsLink.lean · nothing kept beside, the trivial joint, the default
    witnesses and sample (K10Defaults.lean) · n := the sum of the three counts. The two texts are
    cut by program out of `k10_all_five`'s and `k10_all_link`'s hypotheses.
  `k10_heavyAll_of_car`: under `rowsRead Z`: `K10CarAll` gives `AtMgA.K10HeavyAll`
    (K10SeatedOfHeavy.lean): by `k10_all_five` and `k10_all_link`.
  `k10_kind_of_car`: SO: `h.Kind L .K10`: by `k10_kind_of_heavy`.
Limits. NOT "from the head": `rowsRead Z` is no part of the head; reads and `K10CarAll` are
hypotheses. That a payer of the field hCar meets `K10CarAll` at these terms is not shown here.
Nothing is shown of any state: the condition in front may hold of none. Nothing on soundness.

-/
import Johnson.P5J.K10AllFive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts rowSegs)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (K10FirstTie K10Car K10Last k10_last_of_two namesOf noK10
seatK10 written_of_mem
  linksFull_layout onS_of_rowAsks fa_front_same good_cs
  plan_of_shapes stPub layPub begun_at shapesAre_begun)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt tie_at_laid smpDrawn covered_laid hm_at
  plainDue gensDue numBy esOf esOf_nodup esOf_all pSseed)
open VerifiableInference.Desc.First.Close (kLay kbAt layPub_some joint0 joint0_on wit0 brw0 smp0)
open VerifiableInference.Desc.P2Notices (seed_at_K10)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.Desc.First.Close (loFive loSix kbFive kbSix noFiveAt loFive_written
    five_layout
  five_kLay five_corners_at five_entries membersOf hMSub hZSub Corners layAt sizesM sizesZ RowAsks
  ShapesAre hPr_of k10_heavy_of_asks)
open VerifiableInference.Desc.LinkJoin (seatFiveAt plan_seven_five sitsIn_five tie_five_laid SitsIn
  PlanSeven esOf_length k10_rows_due)
open VerifiableInference.Desc.P2Notices (seed_at_five)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option quotPrecheck false in
/-- The first chain's pieces' type. -/
local notation "PC" => Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl
  (Wit (CellsM numsFull) At.Tok MsgT)

set_option quotPrecheck false in
/-- Its statements' type. -/
local notation "ST" => (ProofFile.InstPub × TS) × (Frame.E FR).Str

open Classical in
/-- **WHAT IS LEFT OF K10's OWN DEBT: what stands behind the closing, at the chosen terms.** -/
def AtMgA.K10CarAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop :=
  (∃ mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
    (k10_hM_five h) (k10_hZ_five h)).Sh.par.Cw.nat.Str, ∀ (pw : VerifiableInference.Desc.K9.Where)
    (b : Block TS ProofFile.Cl) (Q : Par) (g0 : OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀
    base : ℕ, IM.k9At Zp 0 = some pw → ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q →
    cF.blocksInOrder[ixK10 0]? = some b → (h.toAtMg.row L)[ixK10 0]? = some (pieceOf (held b) base (dBat
             Q.rows :: dEps :: List.replicate Q.k dTwo) [] (restCap L.e₁ (ixK10 0) (dBat Q.rows :: dEps ::
             List.replicate Q.k dTwo))) → b.place.kind = KindName.K10 → Q.k = g0.k → g0.k = kLay
    (linksFullLit.getD 0 []) (kbAt shapeFull 0 (linksFullLit.getD 0 [])) → (∀ s rs gs' s', b.decide
    s rs gs' = .ok s' → ∃ y, closeFrame (rdK s).1 (rdK s).2.1 (rdK s).2.2 (entries Q) rs = .ok y ∧
    s' = wrK s y.1 y.2) → K10Car (At.cs Zp) loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h)
    (fun _ => False) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
    (k10_hM_five h) (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))
    (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
    h)) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
    (k10_hZ_five h))) (joint0 (At.cs Zp) loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin
    (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0)) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219)
    radFull kbFive (k10_hM_five h) (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK
    Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
    (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
    (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
    kbFive (k10_hM_five h) (k10_hZ_five h)))) (wit0 (At.cs Zp) loFive) (brw0 (At.cs Zp) loFive (gsAt
    0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0)) (nPK Zp cF 0 +
    (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
    h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf
    (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive
    (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp)
    loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) (F0T
    OnBytes.secondHashFunction Zp Np cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt
                0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h) (noFiveAt (At.seats Zp) (At.pseats Zp)))
    [] (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive,
          (seatFiveAt (At.pseats Zp))⟩ i) (smp0 (At.cs Zp) loFive) () () mW (At.arr Zp) (At.ms Zp Z.lay)
    (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf (pSseed (At.cs Zp)
                loFive (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
                (k10_hZ_five h)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five
                h) (k10_hZ_five h) (noFiveAt (At.seats Zp) (At.pseats Zp))) (stPub loFive (noFiveAt (At.seats
                Zp) (At.pseats Zp))) ((layPub_some (no := noFiveAt (At.seats Zp) (At.pseats Zp))
                five_layout).choose) (noFiveAt (At.seats Zp) (At.pseats Zp))) Q b base L.e₁ (ixK10 0)
    (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
    219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)).foldCaller (fun _ => False) (SbV (groupLayK
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (Fin
    (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219)
    radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (pullOf (groupLayK (At.cs Zp) loFive (stageOf
    (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) (ZV (groupLayK (At.cs Zp) loFive
    (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (nPK Zp cF 0 + (esOf
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)).length
    + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219)
    radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0)
    219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp) loFive (stageOf (gsAt
    0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) ((1 : Fin 3), (1 : GE)) (joint0 (At.cs
    Zp) loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF
    0)) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
    (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp)
    loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs
    Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))))
    (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ (wit0 (At.cs Zp) loFive) (brw0 (At.cs Zp)
    loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))
    (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
    (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp)
    loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs
    Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))))
    (dBat (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five
    h) (k10_hZ_five h)).length + nGK Zp cF 0)) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf
    id) (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
    (ixK10 0) b.place (XK h 0) (oAt (ixK10 0)) (noFiveAt (At.seats Zp) (At.pseats Zp)) (h.toAtMg.row
    L) Q.k) ∧
  ∀ (l : ℕ) (_ : 1 ≤ l) (hl : l < 25), ∃ mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) (loAt l)
    (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).Sh.par.Cw.nat.Str, ∀
    (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par) (g0 :
          OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp l = some pw →
    ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 l]? = some b → (h.toAtMg.row
                         L)[ixK10 l]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                         (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) → b.place.kind =
    KindName.K10 → Q.k = g0.k → g0.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l
    (linksFullLit.getD l [])) → (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK
    s).1 (rdK s).2.1 (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) → K10Car (At.cs Zp)
    (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (fun _ => False) (nPK Zp cF l +
    (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf
    (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt
    l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs
    Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))
    (joint0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (Fin (nPK Zp cF
    l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
    (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp
    cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
    (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
    radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (wit0 (At.cs Zp) (loAt l)) (brw0 (At.cs
    Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (Fin (nPK Zp cF l) ⊕ Fin (nGK
    Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l)
    (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
    (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (F0T OnBytes.secondHashFunction Zp Np cF) (seatK10 (loAt l)
                (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l
                h l hl) (k10_hZ_l h l hl) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) [] (At.smp Zp) (fun
                (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l), (seatK10 (loAt l)
                      (At.pseats Zp) l)⟩ i) (smp0 (At.cs Zp) (loAt l)) () () mW (At.arr Zp) (At.ms Zp Z.lay) (dtK
                      (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf (pSseed (At.cs Zp) (loAt
                                  l) (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
                                  (k10_hZ_l h l hl)) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l
                                  h l hl) (k10_hZ_l h l hl) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) (stPub (loAt l)
                                  (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) ((layPub_some (no := noK10 (At.seats Zp) (loAt
                                  l) (At.pseats Zp) l) (linksFull_layout (loAt l) (loAt_mem l hl) (kbW l))).choose) (noK10
                                  (At.seats Zp) (loAt l) (At.pseats Zp) l)) Q b base L.e₁ (ixK10 l)
    (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
    219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).foldCaller (fun _ => False) (SbV
    (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
    (k10_hZ_l h l hl)) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l))) (slV (groupLayK (At.cs Zp) (loAt l)
    (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (pullOf (groupLayK
    (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl)))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l
    hl) (k10_hZ_l h l hl)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
    (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp
    cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
    (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
    radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) ((1 : Fin 3), (1 : GE)) (joint0 (At.cs
    Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (Fin (nPK Zp cF l) ⊕ Fin (nGK
    Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l)
    (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
    (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ (wit0
    (At.cs Zp) (loAt l)) (brw0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf
    (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy
    (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
    (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
    radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf
    (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl))))) (dBat (nPK Zp cF l + (esOf
    (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
    hl)).length + nGK Zp cF l)) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
    (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10
    l) b.place (XK h l) (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)
    (h.toAtMg.row L) Q.k

/-- **K10HeavyAll from what stands behind the closing.** -/
theorem k10_heavyAll_of_car (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z)
    (C : h.K10CarAll L) : h.K10HeavyAll L := by
  intro l hl
  by_cases h0 : l = 0
  · subst h0
    exact k10_all_five h L hrr C.1.choose C.1.choose_spec
  · exact k10_all_link h L hrr l (Nat.pos_of_ne_zero h0) hl
      (C.2 l (Nat.pos_of_ne_zero h0) hl).choose (C.2 l (Nat.pos_of_ne_zero h0) hl).choose_spec

/-- **THE FIELD OF THE KIND K10, FROM THE HEAD, rowsRead Z, reads AND K10CarAll.** -/
theorem k10_kind_of_car (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hrr : rowsRead Z)
    (reads : ∀ (i : ℕ) (a : VerifiableInference.Desc.Place), At.ps[i]? = some a →
      a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (C : h.K10CarAll L) : h.Kind L .K10 :=
  k10_kind_of_heavy h L q1 q2 q3 reads (k10_heavyAll_of_car h L hrr C)

end P5J

#print axioms P5J.k10_heavyAll_of_car
#print axioms P5J.k10_kind_of_car
