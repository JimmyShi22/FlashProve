-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarAll.lean (kind K10; namespace P5J): **THE FIELD hCar OF `K10Heavy`
  AT THE CLOSED CONSTANT's LETTERS, FROM THE HEAD AND «THE ROWS ARE READ» (rowsRead Z)**:
  `hCar_paid_more` | `hCar_paid_five_more` (HCarPaidMore.lean) with the rest of their named premises
  laid in, one theorem a branch. At keep := fun _ => False (nobody is kept beside) and base := the
  seated piece's own base. Theorems.

  `allMain_at`: at 1 ≤ l < 25 every message of loAt l has a main row (allMain_later,
    by the kernel).
  `AtMgA.hCar_all` (1 ≤ l < 25; at loAt l) · `AtMgA.hCar_all_five` (l = 0; at loFive). LAID IN: hk |
    hpl (k10_place) · hbase (k10_base_at) · hbD
    (whole_atAll) · hgood (good_cs, with written_of_mem, gsAt_front,
    linksFull_corners_all | five_corners_at) · hSit (sitsIn_at | sitsIn_five: under
    rowsRead Z) · hDoor · hGf (hDoor_at | hGf_at,
    Johnson/P2LawR/CarriedDoorAtK10.lean) · h2 (carried_second_none and kp_none, at
    keep := fun _ => False).
WHAT IS LEFT, BESIDE THE HEAD h AND rowsRead Z: the free letters' three equations q1 | q2 | q3 and
  the seated piece (hq) · K10's place (hp · hK) · the typed group's hM | hZ (K10Heavy's own letters;
  at the five-list also the six-list's hM₆ | hZ₆) · a seed z₀ and a value v₂ · hA: the joint beside
  holds at (st₀, e₀) whatever the (empty) message: at the trivial joint it is trivial.
Limits. At the second hash function; the full size. No member is shown. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.HCarPaidMore
import Johnson.P2LawR.CarriedDoorAtK10
import Johnson.LPFE1R.SitsInAt
import Johnson.P5J.K10Low
import Johnson.P5J.CodesFullAtMg
import Johnson.Desc.First.Close.Law.StageClosed
import Johnson.Desc.First.Close.Law.CornersKept
import Johnson.Desc.First.Close.Law.CarriedSecondNone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts FoldData bookAt)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (groupLayK namesOf RowAsks noK10 seatK10 rdK ShapesAre
  posOf keptOrd_full maskTree maskPart maskShape maskA maskSkip rdBK wrK LayoutAgrees layAt sizesM
  sizesZ loFive kbFive loSix seatsMain seatsOfLink zero_hr keptOrd_five HCarField hCar_heavy SbV
  slV ZV faK10 Par pullOf placeFull dBat dEps dTwo closeFrame noFiveAt
  linksFull_layout five_layout seatFive noFive noFiveAt_written seatsPlanW
  good_cs written_of_mem linksFull_corners_all five_corners_at loFive_written five_allMain
  carried_second_none kp_none allMainB allMain_later)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt hB_at_k10 ld_at_laid keptRowsAt keptNosOf
  seatFiveAt seatFive_at_laid keptRows_of_pub hr_at_laid row_at_laid batchAt bookAt_of_onQ SitsIn
  planClosedB mWRaw sitsIn_at sitsIn_five gsAt_front)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes atFirstBook atFirstSeats atFirstFits
  placesBelowB)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.First.K2Caller (carryAtZ places_of_promise SeatFitAt doorZ)
open _root_.Tw.K2 (switchNotices)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

theorem allMain_at (l : ℕ) (h1 : 1 ≤ l) (hl : l < 25) : ∀ i, memMain (loAt l) i := by
  have hm : loAt l ∈ linksFullLit.drop 1 := by
    have hn : l < linksFullLit.length := by
      have e : linksFullLit.length = 26 := by decide
      omega
    unfold loAt
    rw [List.getD_eq_getElem _ _ hn]
    obtain ⟨k, rfl⟩ : ∃ k, l = 1 + k := ⟨l - 1, by omega⟩
    rw [← List.getElem_drop (i := 1) (j := k) (h := by simpa using by omega)]
    exact List.getElem_mem _
  have h := List.all_eq_true.1 (List.all_eq_true.1 allMain_later _ hm)
  intro i
  have := h _ (List.get_mem (loAt l) i)
  simpa [memMain] using this

/-- **THE FIELD hCar AT A LINK FROM 1 TO 24, FROM THE HEAD AND «THE ROWS ARE READ».** -/
theorem AtMgA.hCar_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Lf : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = Lf.c₁ :: Lf.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = Lf.c₂ :: Lf.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = Lf.c₃ :: Lf.k₃)
    (hrr : rowsRead Z)
    (q : Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl (Wit (CellsM numsFull) At.Tok MsgT))
    (l : ℕ)
    (h1 : 1 ≤ l)
    (hl : l < 25)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).Z)
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G.Row B ≃
      Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ).sizeB (fun _ => False) (SbV (groupLayK (At.cs Zp) (loAt
      l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) (loAt l)).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G
      ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).sizeB (fun _ =>
      False) (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B)
      (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (smpD : ProofFile.InstPub × TS → (i : Fin (loAt l).length) → Option ((sigOf (At.cs Zp) (loAt l)).om
            i).Smp)
    (σ₀ : (sigOf (At.cs Zp) (loAt l)).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM numsFull))
    (c₀ : (CellsM numsFull))
    (tokOf : ProofFile.InstPub × TS → At.Tok)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).G.A, ((sigOf (At.cs Zp) (loAt l)).om a.1).Z.S), ((sigOf (At.cs Zp) (loAt l)).om
      as.1.1).Z.D → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block TS Cl)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).foldCaller
      (fun _ => False) (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
      (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num) ((1 : Fin
      3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁) (wT (dBat n)) (wT
      dEps) (wT dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 l]? = some p)
    (hK : p.kind = KindName.K10)
    (hq : (h.toAtMg.row Lf)[ixK10 l]? = some q)
    (z₀ : (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num).D)
    (v₂ : Wp)
    (hA : ∀ mm, A₀.relR (st₀, e₀) (mm, v₂)) :
    HCarField (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ (fun _ => False) n num A₀ w₀ w₁ (F0T
      OnBytes.secondHashFunction Zp Np cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l)
                  (stageOf (gsAt l) 219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
      L (At.smp Zp) smpD σ₀ st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l)
      (memMain (loAt l)) (stageOf (gsAt l) 219) radFull (fun i => layAt (sizesM (loAt l) (kbW l))
      i.val) (fun i => layAt (sizesZ (loAt l)) i.val) hM hZ (fun a => kbW l a.1 = true) (strsOf FR
      b.2) (maskTree l) (maskSkip l) (maskA l)) (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b
      q.base ex ix ρ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) O (noK10
      (At.seats Zp) (loAt l) (At.pseats Zp) l) row k' := by
  have hpl : p.link.getD 0 = l := by
    rw [(k10_place l hl p hp).1]
    rfl
  have g := List.all_eq_true.1 gsAt_front l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  have SI := sitsIn_at h hrr hp hK (by rw [hpl]; exact h1) (by rw [hpl]; exact hl)
  rw [hpl] at SI
  have hgood := good_cs (At.cs Zp) h.toAtMg.codes_full (loAt l) (written_of_mem (loAt_mem l hl))
    (gsAt l) g.1 (kbW l) hM hZ (by rw [g.2]; exact linksFull_corners_all _ (loAt_mem l hl) _)
  exact
    h.hCar_paid_more l hl hM hZ (fun _ => False) n num A₀ w₀ w₁ L smpD σ₀ st₀ e₀ decT c₀ tokOf pS Pr
      b q.base ex ix ρ p O row k' hp hK hpl (k10_base_at h Lf q1 q2 q3 (ixK10 l) p hp hK q hq)
      ((P1L20.whole_atAll h Lf q1 q2 q3).2 (ixK10 l) q hq) hgood SI (fun z a hX =>
      VerifiableInference.Desc.P2Notices.hGf_at h hl (a := ((z, a.1), a.2)) hX.1 hX.2.1 hX.2.2) (fun
      z a a' es rs hX hc he => VerifiableInference.Desc.P2Notices.hDoor_at h hl (a := ((z, a.1),
      a.2)) hX.1 hX.2.1 hX.2.2 hc he) (fun z a _ => carried_second_none (groupLayK (At.cs Zp) (loAt
      l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (fun _ => False) _ _ _ _ A₀ _ _ w₀ w₁ L _
      (kp_none (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) _ _ _
      (allMain_at l h1 hl)) z₀ v₂ (hA _))

/-- **THE FIELD hCar AT LINK 0, AT THE FIVE-LIST, FROM THE HEAD AND «THE ROWS ARE READ».** -/
theorem AtMgA.hCar_all_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Lf : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = Lf.c₁ :: Lf.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = Lf.c₂ :: Lf.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = Lf.c₃ :: Lf.k₃)
    (hrr : rowsRead Z)
    (q : Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl (Wit (CellsM numsFull) At.Tok MsgT))
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).Z)
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G.Row B ≃ Fin
      n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).sizeB (fun _ => False) (SbV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) loFive).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB (fun _ =>
      False) (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp Wp)
    (L : List (BatFoldCaller GE))
    (smpD : ProofFile.InstPub × TS → (i : Fin loFive.length) → Option ((sigOf (At.cs Zp) loFive).om
            i).Smp)
    (σ₀ : (sigOf (At.cs Zp) loFive).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × TS → Option (CellsM numsFull))
    (c₀ : (CellsM numsFull))
    (tokOf : ProofFile.InstPub × TS → At.Tok)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).G.A, ((sigOf (At.cs Zp) loFive).om a.1).Z.S), ((sigOf (At.cs Zp) loFive).om as.1.1).Z.D →
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).Sh.Cin.J → GE)
    {Cl : Type}
    (Pr : Par)
    (b : Block TS Cl)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller
      (fun _ => False) (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ) B) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE))
      A₀ (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT
      dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 0]? = some p)
    (hK : p.kind = KindName.K10)
    (hq : (h.toAtMg.row Lf)[ixK10 0]? = some q)
    (z₀ : (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num).D)
    (v₂ : Wp)
    (hA : ∀ mm, A₀.relR (st₀, e₀) (mm, v₂)) :
    HCarField (At.cs Zp) loFive (gsAt 0) kbFive hM hZ (fun _ => False) n num A₀ w₀ w₁ (F0T
      OnBytes.secondHashFunction Zp Np cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt
                  0) 219) radFull kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) L (At.smp Zp) smpD σ₀
      st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf
      (gsAt 0) 219) radFull (fun i => layAt (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ
      loFive) i.val) hM hZ (fun a => kbFive a.1 = true) (strsOf FR b.2) (maskTree 0) (maskSkip 0)
      (maskA 0)) (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b q.base ex ix ρ (At.N Zp cF)
      (mgAtAll h) fullLinks At.ps (ixK10 0) p (XK h 0) O (noFiveAt (At.seats Zp) (At.pseats Zp)) row
      k' := by
  have hl : (0 : ℕ) < 25 := by decide
  have hpl : p.link.getD 0 = 0 := by
    rw [(k10_place 0 hl p hp).1]
    rfl
  have g := List.all_eq_true.1 gsAt_front 0 (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  have SI := sitsIn_five h hrr hp hK hpl
  have hgood := good_cs (At.cs Zp) h.toAtMg.codes_full loFive loFive_written (gsAt 0) g.1 kbFive hM
    hZ (five_corners_at (gsAt 0) g.2)
  exact
    h.hCar_paid_five_more hM hZ hM₆ hZ₆ (fun _ => False) n num A₀ w₀ w₁ L smpD σ₀ st₀ e₀ decT c₀
      tokOf pS Pr b q.base ex ix ρ p O row k' hp hK hpl (k10_base_at h Lf q1 q2 q3 (ixK10 0) p hp hK
      q hq) ((P1L20.whole_atAll h Lf q1 q2 q3).2 (ixK10 0) q hq) hgood SI (fun z a hX =>
      VerifiableInference.Desc.P2Notices.hGf_at h hl (a := ((z, a.1), a.2)) hX.1 hX.2.1 hX.2.2) (fun
      z a a' es rs hX hc he => VerifiableInference.Desc.P2Notices.hDoor_at h hl (a := ((z, a.1),
      a.2)) hX.1 hX.2.1 hX.2.2 hc he) (fun z a _ => carried_second_none (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (fun _ => False) _ _ _ _ A₀ _ _ w₀ w₁ L _
      (kp_none (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) _ _ _
      five_allMain) z₀ v₂ (hA _))

end P5J

#print axioms P5J.allMain_at
#print axioms P5J.AtMgA.hCar_all
#print axioms P5J.AtMgA.hCar_all_five
