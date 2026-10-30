-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/HCarPaidMore.lean (kind K10; namespace P5J): `hCar_paid` (HCarPaid.lean)
  AND `hCar_paid_five` (HCarPaidFive.lean) WITH FIVE MORE OF THEIR NAMED PREMISES LAID IN: hS · hpos
  · hPC (three theorems from the head, in other files: seatFit_at_head | seatFit_five_at_head ·
  pos_at_head · planClosed_at_head | planClosed_five_at_head: Johnson/IMR/K10SeatFit.lean,
  K10SeatFitFive.lean, K10Pos.lean, K10PlanClosed.lean) · hLA (
  linksFull_layout | five_layout) · hle (a closed line of this file). Theorems. No other file
  turns.

  `hLA_full`: LayoutAgrees (loAt l) (kbW l): the l-th written list is one of the written lists
    (loAt_mem, Johnson/P5J/K10HXAt.lean).
  `hle_full`: (gsAt l).h ≤ (gsAt l).k at every l < 25: by the kernel, at the written table;
    `hle_can_fail`: a negative line.
  `AtMgA.hS_five`, `AtMgA.hPC_five`: `seatFit_five_at_head`, `planClosed_five_at_head` stand at the
    written seats and numbers (seatFive · noFive): carried to seatFiveAt (At.pseats Zp) · noFiveAt
    (At.seats Zp) (At.pseats Zp) by «the plan's seats are the written ones» (the head's own).
  `AtMgA.hCar_paid_more`, `AtMgA.hCar_paid_five_more`: **the field hCar of K10Heavy at the closed
    constant's letters, with these laid in.**
Limits. NAMED PREMISES LEFT: the place's three (hp · hk · hpl) · hbase · hbD · hgood · hSit · hGf ·
  hDoor · h2 (at the five-list also hM₆ | hZ₆). hCar_paid_more at l = 0 stands at the six-list: take
  it as idle there; hCar_paid_five_more is link 0's. At the second hash function. Nothing on
  soundness.
-/
import Johnson.Desc.First.Link.Law.HCarPaidFive
import Johnson.IMR.K10SeatFit
import Johnson.IMR.K10SeatFitFive
import Johnson.IMR.K10Pos
import Johnson.IMR.K10PlanClosed
import Johnson.Desc.First.Close.Law.LayoutDrawn

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
  linksFull_layout five_layout seatFive noFive noFiveAt_written seatsPlanW)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt hB_at_k10 ld_at_laid keptRowsAt keptNosOf
  seatFiveAt seatFive_at_laid keptRows_of_pub hr_at_laid row_at_laid batchAt bookAt_of_onQ SitsIn
  planClosedB mWRaw)
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

theorem hLA_full (l : ℕ) (hl : l < 25) : LayoutAgrees (loAt l) (kbW l) :=
  linksFull_layout _ (loAt_mem l hl) _

theorem hle_fullB : (List.range 25).all (fun l => decide ((gsAt l).h ≤ (gsAt l).k)) = true := by
  decide +kernel

/-- A negative line: the comparison the other way about does not hold at every link. -/
theorem hle_can_fail : (List.range 25).all (fun l => decide ((gsAt l).k ≤ (gsAt l).h)) = false := by
  decide +kernel

theorem hle_full (l : ℕ) (hl : l < 25) : (gsAt l).h ≤ (gsAt l).k :=
  of_decide_eq_true (List.all_eq_true.1 hle_fullB l (List.mem_range.2 hl))

theorem AtMgA.hS_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i : Fin loFive.length) :
    SeatFitAt (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) i := by
  rw [seatFive_at_laid h.toAtMg.scope h.toAtMg.laid]
  exact IM.K10.seatFit_five_at_head h.toAtMg i

theorem AtMgA.hPC_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i : Fin loFive.length) :
    planClosedB (F0T OnBytes.secondHashFunction Zp Np cF) LFull (noFiveAt (At.seats Zp) (At.pseats Zp) i)
      (seatFiveAt (At.pseats Zp) i) (aOf (At.cs Zp) (loFive.get i).1) = true := by
  have e1 : At.pseats Zp = P5T.psFull := h.toAtMg.laid.seats h.toAtMg.scope
  have e2 : At.seats Zp = seatsPlanW := by
    unfold At.seats
    rw [e1]
  rw [seatFive_at_laid h.toAtMg.scope h.toAtMg.laid, e1, e2, noFiveAt_written]
  exact IM.K10.planClosed_five_at_head h.toAtMg (ld_at_laid h.toAtMg.scope h.toAtMg.laid) i

/-- **hCar_paid WITH hS · hpos · hPC · hLA · hle LAID IN.** -/
theorem AtMgA.hCar_paid_more (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (l : ℕ)
    (hl : l < 25)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).Z)
    (keep : (sigOf (At.cs Zp) (loAt l)).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G.Row B ≃
      Fin n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) (loAt l)).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G
      ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
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
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).foldCaller
      keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num) ((1 : Fin 3), (1 :
      GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT
      dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 l]? = some p)
    (hk : p.kind = KindName.K10)
    (hpl : p.link.getD 0 = l)
    (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 l]?)
    (hbD : base ≤ D.t₁)
    (hgood : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).Good)
    (hSit : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l))
    (hGf : ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) → ∀ Gf, (rdK a.1).2.1.groups[(rdK
      a.1).2.1.link]? = some Gf → Gf.k = (gsAt l).k ∧ Gf.h = (gsAt l).h)
    (hDoor : ∀ z (a a' : TS × (Frame.E FR).Str) es rs, XK h l ((z, a.1), a.2) → closeFrame (rdK
      a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 es rs = .ok (rdBK a'.1) → a'.1 = wrK a.1 (rdBK a'.1).1
      (rdBK a'.1).2 → (∀ t, doorZ Zp l a'.1 = some t → (ProofFile.pAtK2 Zp l).stands = .head → ∀ b,
      a'.1.here ≠ .head b) ∧ ∀ t fx', doorZ Zp l a'.1 = some t →
      VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp l) t = some fx' → ∃ Bk,
      VerifiableInference.Desc.First.K2.bookAt (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Zp
      l)).firstTree fx'.st t.book t.roots (switchNotices fx'.T fx'.others) = some Bk)
    (h2 : ∀ z (a : TS × (Frame.E FR).Str), (XK h l) ((z, a.1), a.2) → ∃ (zz : (ZV (groupLayK (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num).D) (v : ((sigOf (At.cs Zp)
      (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
      (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n num)).kp).Wit ×
      Wp), (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n
      num)).kp).over A₀).relR ((batX ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) n
      num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁)
      (faK10 (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l)
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (namesOf (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l)
      (At.pseats Zp) l)) keep (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ)) n num ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt
      l).k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l)
      (memMain (loAt l)) (stageOf (gsAt l) 219) radFull (fun i => layAt (sizesM (loAt l) (kbW l))
      i.val) (fun i => layAt (sizesZ (loAt l)) i.val) hM hZ (fun a => (kbW l) a.1 = true) (strsOf FR
      b.2) (maskTree l) (maskSkip l) (maskA l)) z a).1 zz).2, ((ldBrG (groupLayK (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) n num)).kp E₀).map (e₀, wordsOf (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) (loAt l) (seatK10
                  (loAt l) (At.pseats Zp) l) (strsOf FR a.2))).2) v) :
    HCarField (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp
      Np cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) L (At.smp Zp) smpD σ₀
      st₀ e₀ (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l) (memMain (loAt l)) (stageOf
      (gsAt l) 219) radFull (fun i => layAt (sizesM (loAt l) (kbW l)) i.val) (fun i => layAt (sizesZ
      (loAt l)) i.val) hM hZ (fun a => kbW l a.1 = true) (strsOf FR b.2) (maskTree l) (maskSkip l)
      (maskA l)) (At.arr Zp) (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF)
      (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) O (noK10 (At.seats Zp) (loAt l) (At.pseats
      Zp) l) row k' :=
  h.hCar_paid l hl hM hZ keep n num A₀ w₀ w₁ L smpD σ₀ st₀ e₀ decT c₀ tokOf pS Pr b base ex ix ρ p O
    row k' hp hk hpl hbase hbD hgood (hLA_full l hl) (hle_full l hl) hSit (fun b =>
    IM.K10.seatFit_at_head h.toAtMg hl b.1) (IM.K10.pos_at_head h.toAtMg hl) (fun b =>
    IM.K10.planClosed_at_head h.toAtMg (ld_at_laid h.toAtMg.scope h.toAtMg.laid) hl b.1) hGf hDoor
    h2

/-- **hCar_paid_five WITH hS · hpos · hPC · hLA · hle LAID IN.** -/
theorem AtMgA.hCar_paid_five_more (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (hM₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).C)
    (hZ₆ : ∀ i, memMain (loAt 0) i → ((loAt 0).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt
      0).get i).1 = (stageOf (gsAt 0) 219).Z)
    (keep : (sigOf (At.cs Zp) loFive).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (n : ℕ)
    (num : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G.Row B ≃ Fin
      n)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)
      n num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) loFive).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp Wp)
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
    (base : ℕ)
    (ex : (i : ℕ) → (ds : List RDT) → (ProofFile.InstPub × TS) × (Frame.E FR).Str → Iop.Tr (uLT (ckP .two)
            ds) → Wit (CellsM numsFull) At.Tok MsgT → Wit (CellsM numsFull) At.Tok MsgT)
    (ix : ℕ)
    (ρ : Rd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (hp : At.ps[ixK10 0]? = some p)
    (hk : p.kind = KindName.K10)
    (hpl : p.link.getD 0 = 0)
    (hbase : base = (At.N Zp cF).treesAt At.ps[ixK10 0]?)
    (hbD : base ≤ D.t₁)
    (hgood : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).Good)
    (hSit : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 0)) loFive (seatFiveAt (At.pseats Zp)))
    (hGf : ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) → ∀ Gf, (rdK a.1).2.1.groups[(rdK
      a.1).2.1.link]? = some Gf → Gf.k = (gsAt 0).k ∧ Gf.h = (gsAt 0).h)
    (hDoor : ∀ z (a a' : TS × (Frame.E FR).Str) es rs, XK h 0 ((z, a.1), a.2) → closeFrame (rdK
      a.1).1 (rdK a.1).2.1 (rdK a.1).2.2 es rs = .ok (rdBK a'.1) → a'.1 = wrK a.1 (rdBK a'.1).1
      (rdBK a'.1).2 → (∀ t, doorZ Zp 0 a'.1 = some t → (ProofFile.pAtK2 Zp 0).stands = .head → ∀ b,
      a'.1.here ≠ .head b) ∧ ∀ t fx', doorZ Zp 0 a'.1 = some t →
      VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) t = some fx' → ∃ Bk,
      VerifiableInference.Desc.First.K2.bookAt (VerifiableInference.Desc.First.K2.par9 (ProofFile.pAtK2 Zp
      0)).firstTree fx'.st t.book t.roots (switchNotices fx'.T fx'.others) = some Bk)
    (h2 : ∀ z (a : TS × (Frame.E FR).Str), (XK h 0) ((z, a.1), a.2) → ∃ (zz : (ZV (groupLayK (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num).D) (v : ((sigOf (At.cs Zp)
      loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp).Wit × Wp), (((sigOf (At.cs Zp)
      loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB
      keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num)).kp).over A₀).relR ((batX
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller keep
      (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (faK10 (F0T OnBytes.secondHashFunction Zp Np
      cF) (At.cs Zp) loFive (seatFiveAt (At.pseats Zp)) (groupLayK (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) keep (pullOf (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ)) n num ((1 : Fin 3), (1 : GE)) A₀ (placeFull
      (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁ L smpD σ₀ st₀ e₀ (fun b : TS × (Frame.E FR).Str
      => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf (gsAt 0) 219) radFull (fun i => layAt
      (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ loFive) i.val) hM hZ (fun a => kbFive
      a.1 = true) (strsOf FR b.2) (maskTree 0) (maskSkip 0) (maskA 0)) z a).1 zz).2, ((ldBrG
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G ((groupLayK (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ) n num)).kp E₀).map (e₀, wordsOf (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp)
      loFive (seatFiveAt (At.pseats Zp)) (strsOf FR a.2))).2) v) :
    HCarField (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np
      cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) L (At.smp Zp) smpD σ₀ st₀ e₀ (fun b : TS
      × (Frame.E FR).Str => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf (gsAt 0) 219) radFull
      (fun i => layAt (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ loFive) i.val) hM hZ
      (fun a => kbFive a.1 = true) (strsOf FR b.2) (maskTree 0) (maskSkip 0) (maskA 0)) (At.arr Zp)
      (At.ms Zp Z.lay) decT c₀ tokOf pS Pr b base ex ix ρ (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) p (XK h 0) O (noFiveAt (At.seats Zp) (At.pseats Zp)) row k' :=
  h.hCar_paid_five hM hZ hM₆ hZ₆ keep n num A₀ w₀ w₁ L smpD σ₀ st₀ e₀ decT c₀ tokOf pS Pr b base ex
    ix ρ p O row k' hp hk hpl hbase hbD hgood five_layout (hle_full 0 (by decide)) hSit (fun b =>
    h.hS_five b.1) (IM.K10.pos_at_head h.toAtMg (by decide)) (fun b => h.hPC_five b.1) hGf hDoor h2

end P5J

#print axioms P5J.hLA_full
#print axioms P5J.hle_fullB
#print axioms P5J.hle_can_fail
#print axioms P5J.hle_full
#print axioms P5J.AtMgA.hS_five
#print axioms P5J.AtMgA.hPC_five
#print axioms P5J.AtMgA.hCar_paid_more
#print axioms P5J.AtMgA.hCar_paid_five_more
