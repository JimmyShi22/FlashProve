-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K10CarAllPaid.lean (kind K10; namespace P5J): **`AtMgA.K10CarAll h L`
  (Johnson/P5J/K10Top.lean: what is left of K10's own debt beneath the closing's files' top: «what
  stands behind the closing, at the chosen terms», at link 0 at the five-list and at the links 1 to
  24), TO THE LETTER, FROM THE HEAD, THE FREE LETTERS' THREE EQUATIONS AND «THE ROWS ARE READ».** By
  `hCar_all` | `hCar_all_five` (HCarAll.lean), at those files' chosen free letters. Theorems. No
  other file turns.

  `car_of_field`: `HCarField ‹the 45›` (HCarField.lean) gives `K10Car ‹the 45›`
    (Johnson/Desc/First/Close/Law/K10LastTwo.lean): both are the field hCar's own text.
  `AtMgA.k10CarAll_paid`: **h.K10CarAll L.** THE FRESH MASK's WORD THAT IS CHOSEN (the ∃ in front):
    fun b => mWRaw … (strsOf FR b.2) (maskTree l) (maskSkip l) (maskA l): it hangs on l alone; Lean
    finds it from hCar_all's end. The seed is 0; the value beside is (); the joint beside is those
    files' trivial one (joint0_relR).
  `AtMgA.k10_kind_paid`: **h.Kind L .K10**: those files' top (`k10_kind_of_car`) with K10CarAll laid
    in: from the head, q1 | q2 | q3, rowsRead Z and that top's own premise «reads» (the fifth tie at
    K10's places).
Limits. The head h, q1 | q2 | q3 and rowsRead Z are premises. No member is shown. At the format's
  second hash function; the full size. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.HCarAll
import Johnson.P5J.K10Top

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.First.Close

open scoped ENNReal
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Tie.Pv.Fold OnBytes.Flat OnBytes.Maker Iop IOR
open Prob Run KObj Johnson.Pack Johnson.G
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H
open VerifiableInference.Desc.Sound
open Johnson.Top.H.ArrAdd (FreeAt)
open OnBytes.PscRun (drawnOf)
open VerifiableInference.Desc.K9 (recOf putRec)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.First (Numbers Item Meaning ModelPart rowSays wordsAtFirst laysSeats)

local notation "fx1" => ((1 : Fin 3), (1 : GE))
local notation "S1" => VerifiableInference.Desc.First.S

theorem car_of_field
    {cs : OnBytes.Codes}
    {lo : List (OracleShape × ℕ)}
    {gs : GroupSize}
    {kb : Fin lo.length → Bool}
    {hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain cs (lo.get i).1 = (stageOf gs
      219).C}
    {hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask cs (lo.get i).1 = (stageOf gs
      219).Z}
    {keep : (sigOf cs lo).O → Prop}
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    {n : ℕ}
    {num : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n}
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    {A₀ : Rels Kc St₀ E₀ (((sigOf cs lo).sub ((groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp)}
    {w₀ : (sigOf cs lo).Wit × Wp}
    {w₁ : LdBrW (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ).sizeB keep (SbV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) B)
      (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK cs lo (stageOf gs
      219) radFull kb hM hZ))) (ZV (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ) n num)).kp
      Wp}
    {Xi : Type}
    {Gd : FileDescription Xi}
    {seat : Fin lo.length → ℕ × ℕ}
    {Nm : SlotNames (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ)}
    {L : List (BatFoldCaller GE)}
    {Pz : Type}
    {smpS : Pz × S1 → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) → Option
      ((sigOf cs s.l).om i).Smp}
    {smpD : Pz × S1 → (i : Fin lo.length) → Option ((sigOf cs lo).om i).Smp}
    {σ₀ : (sigOf cs lo).Smp}
    {st₀ : St₀}
    {e₀ : E₀.Str}
    {F : Frame}
    {mW : S1 × F.E.Str → (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Sh.par.Cw.nat.Str}
    {Cells Tok : Type}
    {arr : ℕ → ℕ → ℕ}
    {ms : List Mem}
    {decT : (ℕ → Option (ℕ × List UInt64)) → Pz × S1 → Option Cells}
    {c₀ : Cells}
    {tokOf : Pz × S1 → Tok}
    {pS : ∀ as : (Σ a : (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).G.A, ((sigOf cs lo).om
      a.1).Z.S), ((sigOf cs lo).om as.1.1).Z.D → (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ).Sh.Cin.J → GE}
    {Cl : Type}
    {Pr : Par}
    {b : Block S1 Cl}
    {base : ℕ}
    {ex : (i : ℕ) → (ds : List RDT) → (Pz × S1) × F.E.Str → Iop.Tr (uLT (ckP .two) ds) → Wit Cells
      Tok MsgT → Wit Cells Tok MsgT}
    {ix : ℕ}
    {ρ : Rd ((groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK cs
      lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK cs lo (stageOf gs 219) radFull kb hM
      hZ) (pullOf (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK cs lo
      (stageOf gs 219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC
      (placeFull gs.k).bZ w₀ w₁) (wT (dBat n)) (wT dEps) (wT dTwo)}
    {Nu : Numbers}
    {Mg : Meaning Pz (Wit Cells Tok MsgT)}
    {links : List ModelPart}
    {ps : List Place}
    {k : ℕ}
    {p : Place}
    {X : (Pz × S1) × F.E.Str → Prop}
    {O : List Item}
    {no : Fin lo.length → ℕ}
    {row : List (Piece (ckP .two) F (Pz × S1) Cl (Wit Cells Tok MsgT))}
    {k' : ℕ}
    (H : HCarField cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀ e₀ mW arr ms
      decT c₀ tokOf pS Pr b base ex ix ρ Nu Mg links ps k p X O no row k') :
    K10Car cs lo gs kb hM hZ keep n num A₀ w₀ w₁ Gd seat Nm L smpS smpD σ₀ st₀ e₀ mW arr ms decT c₀
      tokOf pS Pr b base ex ix ρ Nu Mg links ps k p X O no row k' := ⟨H⟩

end VerifiableInference.Desc.First.Close

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
open VerifiableInference.Desc.First.Close (K10Car joint0_relR car_of_field)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
/-- The first chain's frame at the seated term. -/
local notation "FR" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

set_option maxHeartbeats 8000000 in
open Classical in
/-- **WHAT IS LEFT OF K10's OWN DEBT BENEATH THE TOP.** -/
theorem AtMgA.k10CarAll_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hrr : rowsRead Z) :
    h.K10CarAll L := by
  refine ⟨⟨
    (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) loFive (memMain loFive) (stageOf (gsAt 0)
      219) radFull (fun i => layAt (sizesM loFive kbFive) i.val) (fun i => layAt (sizesZ loFive)
      i.val) (k10_hM_five h) (k10_hZ_five h) (fun a => kbFive a.1 = true) (strsOf FR b.2) (maskTree
      0) (maskSkip 0) (maskA 0)),
    ?_⟩, fun l h1 hl => ⟨
    (fun b : TS × (Frame.E FR).Str => mWRaw (At.cs Zp) (loAt l) (memMain (loAt l)) (stageOf (gsAt l)
      219) radFull (fun i => layAt (sizesM (loAt l) (kbW l)) i.val) (fun i => layAt (sizesZ (loAt
      l)) i.val) (k10_hM_l h l hl) (k10_hZ_l h l hl) (fun a => kbW l a.1 = true) (strsOf FR b.2)
      (maskTree l) (maskSkip l) (maskA l)),
    ?_⟩⟩
  · intro _ b _ _ _ _ _ _ hfl hS hBK _ _ _
    exact car_of_field
      (h.hCar_all_five L q1 q2 q3 hrr _ (k10_hM_five h) (k10_hZ_five h) (k10_hM_l h 0 (by decide))
        (k10_hZ_l h 0 (by decide)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k10_place_at h _ b
        hfl) hBK hS (0 : GE) () (fun mm => joint0_relR _ _ _ _ _ _ _ _ _ (mm, ())))
  · intro _ b _ _ _ _ _ _ hfl hS hBK _ _ _
    exact car_of_field
      (h.hCar_all L q1 q2 q3 hrr _ l h1 hl (k10_hM_l h l hl) (k10_hZ_l h l hl) _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ (k10_place_at h _ b hfl) hBK hS (0 : GE) () (fun mm => joint0_relR _
        _ _ _ _ _ _ _ _ (mm, ())))

/-- **THE FIELD OF THE KIND K10**: the closing's files' top (`k10_kind_of_car`) with K10CarAll laid
in. -/
theorem AtMgA.k10_kind_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (hrr : rowsRead Z)
    (reads : ∀ (i : ℕ) (a : VerifiableInference.Desc.Place), At.ps[i]? = some a →
      a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) : h.Kind L .K10 :=
  k10_kind_of_car h L q1 q2 q3 hrr reads (h.k10CarAll_paid L q1 q2 q3 hrr)

end P5J

#print axioms VerifiableInference.Desc.First.Close.car_of_field
#print axioms P5J.AtMgA.k10CarAll_paid
#print axioms P5J.AtMgA.k10_kind_paid
