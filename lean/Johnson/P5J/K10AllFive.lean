-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10AllFive.lean: AT THE CLOSED CONSTANT, AT LINK 0, AT THE FIVE-LIST: WHAT
`AtMgA.K10HeavyAll` (K10SeatedOfHeavy.lean, beside this file) ASKS AT THAT LINK, FROM THE HEAD,
`rowsRead Z` AND ONE DEBT: `K10Car`. Four statements and their proofs: calls: the laps of the links
1 to 24 (K10HeavyLinkN.lean, K10TieLink.lean, K10ExistsLink.lean, K10AllLink.lean), at link 0's
letters.

  LINK 0's LETTERS: lo := `loFive` · gs := `gsAt 0` · kb := `kbFive` · seat := `seatFiveAt
    (At.pseats Zp)` · no := `noFiveAt (At.seats Zp) (At.pseats Zp)` · the rest as at the other
    links. Why the five-list: at the six-list the one message that is no member would be carried
    beside whatever is kept, and its word has no witness behind the closing.
  `k10_heavy_five_n`: `K10Last` gives `K10Heavy`, n a letter: fourteen fields by theorems,
    hn57 handed on. `k10_tie_five`: the first tie, under seed. `k10_exists_five`: the typed letters
    exhibited. `k10_all_five`: from the head, `rowsRead Z` and `K10Car` at the chosen free letters:
    the existence at n := Q.rows; seed by `seed_at_five`.
The statements are made by the program that made the other links', at these letters.
Limits. `K10Car` stands; so does `rowsRead Z`, which is no part of the head. Nothing is shown of any
state. Nothing on soundness.

-/
import Johnson.P5J.K10FiveFacts

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

/-- **FOURTEEN OF THE SEVENTEEN BY THEOREMS, ONE HANDED ON, AT LINK 0; n A LETTER.** -/
theorem k10_heavy_five_n (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p) (hK : p.kind =
    KindName.K10)
    (b : Block TS ProofFile.Cl) (Q : Par) (base : ℕ) (hQ : Q.k = (gsAt 0).k) (n : ℕ) (h57 : n ≤ 2 ^ 57)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (keep : (sigOf (At.cs Zp) loFive).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
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
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) loFive).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ).Sh.par.Cw.nat.Str)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).G.A, ((sigOf (At.cs Zp) loFive).om a.1).Z.S), ((sigOf (At.cs Zp) loFive).om as.1.1).Z.D →
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).Sh.Cin.J → GE)
    (A : K10Last (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp
      Np cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) Lc (At.smp Zp) (fun (a : ProofFile.InstPub ×
      TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive, (seatFiveAt (At.pseats Zp))⟩ i) σ₀ st₀
      e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape
      0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 0) (VerifiableInference.Desc.First.Close.realRd
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller keep
      (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (dBat n) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 0) p (XK h 0) (oAt (ixK10 0)) (noFiveAt
      (At.seats Zp) (At.pseats Zp)) (h.toAtMg.row L) Q.k) :
    K10Heavy (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np
      cF) (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) Lc (At.smp Zp) (fun (a : ProofFile.InstPub ×
      TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive, (seatFiveAt (At.pseats Zp))⟩ i) σ₀ st₀
      e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape
      0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 0) (VerifiableInference.Desc.First.Close.realRd
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).foldCaller keep
      (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) B) (slV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ w₀ w₁) (dBat n) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 0) p (XK h 0) (oAt (ixK10 0)) (noFiveAt
      (At.seats Zp) (At.pseats Zp)) (h.toAtMg.row L) Q.k :=
  { hen := loFive_written
    hgs := gs0_ok.1
    hC := k10_corners_five
    hV := k10_hV_at Zp loFive _ fun i => tie_five_laid h.toAtMg i
    hPr := hPr_of (At.cs Zp) loFive (gsAt 0) gs0_ok.1 kbFive hM hZ Q hQ
    hn57 := h57
    hSit := (k10_seven_five h hrr p hp hK).hSit
    hAl := (k10_seven_five h hrr p hp hK).hAl
    hHit := (k10_seven_five h hrr p hp hK).hHit
    hAlM := (k10_seven_five h hrr p hp hK).hAlM
    hGrp := (k10_seven_five h hrr p hp hK).hGrp
    hi1 := (k10_seven_five h hrr p hp hK).hi1
    hi2 := (k10_seven_five h hrr p hp hK).hi2
    hX := h.hX_five_head p hp hM hZ (k10_hM_l h 0 (by omega)) (k10_hZ_l h 0 (by omega))
    hCfX := k10_hCfX_at h 0 loFive _ (k10_sits_five h hrr p hp hK)
    hCar := A.hCar
    hOn := A.hOn }

open Classical in
/-- **THE FIRST TIE AT LINK 0, UNDER seed.** -/
theorem k10_tie_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 0]? = some p) (hK : p.kind =
    KindName.K10)
    (b : Block TS ProofFile.Cl) (Q : Par) (base : ℕ)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (keep : (sigOf (At.cs Zp) loFive).O → Prop)
    [DecidablePred keep]
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0)
      (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ)))).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) loFive).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕
      Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy
      (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ) (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)))).kp Wp)
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) loFive).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ).Sh.par.Cw.nat.Str)
    (L₀ : GroupLayout)
    (h0 : layPub loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) = some L₀)
    (hA : A₀.on (st₀, e₀))
    (seed : ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) → ∀ i : Fin loFive.length,
      memMain loFive i → ∃ (ρ : (Fin (bitsZ (At.cs Zp) (loFive.get i).1) → GE) × Units GE) (y : GE),
      VerifiableInference.Desc.K1.SeedIs (At.cs Zp) (loFive.get i).1 a.1.st (noFiveAt (At.seats Zp)
      (At.pseats Zp) i) ρ y) :
    K10FirstTie (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep (nPK Zp cF 0 + (esOf (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK
      Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ)) A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF)
      (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) Lc (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i =>
      smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive, (seatFiveAt (At.pseats Zp))⟩ i) σ₀ st₀ e₀ mW
      (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0)
      L.c₀ At.tokOf (pSseed (At.cs Zp) loFive (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
      (noFiveAt (At.seats Zp) (At.pseats Zp))) (stPub loFive (noFiveAt (At.seats Zp) (At.pseats
      Zp))) L₀ (noFiveAt (At.seats Zp) (At.pseats Zp))) Q b base L.e₁ (ixK10 0)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ))) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ
      w₀ w₁) (dBat (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).length + nGK Zp cF 0)) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) p (XK h 0) (oAt (ixK10 0)) (noFiveAt (At.seats Zp) (At.pseats Zp)) (h.toAtMg.row L)
      Q.k := by
  refine ⟨fun z a hx => ?_⟩
  exact onS_of_rowAsks (Pr := Q) (z := z) (a := a) (Nu := At.N Zp cF) (O := oAt (ixK10 0)) (m := 0)
    (hX := k10_hX_five_l h p hp hM hZ z a hx) (hP := rfl) (hN := rfl)
    (front := fa_front_same (hV := k10_hV_at Zp loFive _ fun i => tie_five_laid h.toAtMg i)
      (z := z) (a := a) (hc := k10_hCfX_at h 0 loFive _ (k10_sits_five h hrr p hp hK) z a hx)
      (hA := hA) ..)
    (five := k10_five_l h (atMgR_rch_of_head h).choose (atMgR_rch_of_head h).choose_spec.fold 0
      (by omega) p hp (k10_hM_l h 0 (by omega)) (k10_hZ_l h 0 (by omega)) Q z a hx)
    (hm := hm_at (by omega)) (hc := covered_laid h.scope h.laid (by omega))
    (good := good_cs (At.cs Zp) h.toAtMg.codes_full loFive loFive_written (gsAt 0) gs0_ok.1 kbFive
      hM hZ k10_corners_five)
    (agrees := five_layout) (kL := kL_five) (h0 := (kh_at 0 (by omega)).2)
    (apart := h.toAtMg.hinj_five_at) (tie := fun i _ => tie_five_laid h.toAtMg i)
    (seed := seed z a hx)
    (plan := fun Gr lay hG hlay as D => plan_of_shapes (At.cs Zp) (stageOf (gsAt 0) 219) radFull hM
      hZ _ h0 (begun_at _ Gr hG) hlay (shapesAre_begun _ (k10_hinge_five h z a hx Gr hG)) as D) ..

open Classical in
/-- **THE TYPED LETTERS, EXHIBITED, AT LINK 0.** -/
theorem k10_exists_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z) (b : Block TS
                ProofFile.Cl)
    (hp : At.ps[ixK10 0]? = some b.place) (hK : b.place.kind = KindName.K10) (Q : Par)
    (base : ℕ) (hQ : Q.k = (gsAt 0).k)
    (hM : ∀ i, memMain loFive i → (loFive.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).C)
    (hZ : ∀ i, memMain loFive i → (loFive.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (loFive.get i).1
      = (stageOf (gsAt 0) 219).Z)
    (keep : (sigOf (At.cs Zp) loFive).O → Prop)
    [DecidablePred keep]
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) loFive).sub ((groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0)
      (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ)))).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) loFive).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).G
      ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕
      Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ) (pullOf (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy
      (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ) (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ)))).kp Wp)
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) loFive).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ).Sh.par.Cw.nat.Str)
    (L₀ : GroupLayout)
    (h0 : layPub loFive kbFive (noFiveAt (At.seats Zp) (At.pseats Zp)) = some L₀)
    (hA : A₀.on (st₀, e₀))
    (seed : ∀ z (a : TS × (Frame.E FR).Str), XK h 0 ((z, a.1), a.2) → ∀ i : Fin loFive.length,
      memMain loFive i → ∃ (ρ : (Fin (bitsZ (At.cs Zp) (loFive.get i).1) → GE) × Units GE) (y : GE),
      VerifiableInference.Desc.K1.SeedIs (At.cs Zp) (loFive.get i).1 a.1.st (noFiveAt (At.seats Zp)
      (At.pseats Zp) i) ρ y)
    (Car : K10Car (At.cs Zp) loFive (gsAt 0) kbFive hM hZ keep (nPK Zp cF 0 + (esOf (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0)
      (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ)) A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF)
      (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp))) Lc (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i =>
      smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive, (seatFiveAt (At.pseats Zp))⟩ i) σ₀ st₀ e₀ mW
      (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0)
      L.c₀ At.tokOf (pSseed (At.cs Zp) loFive (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ
      (noFiveAt (At.seats Zp) (At.pseats Zp))) (stPub loFive (noFiveAt (At.seats Zp) (At.pseats
      Zp))) L₀ (noFiveAt (At.seats Zp) (At.pseats Zp))) Q b base L.e₁ (ixK10 0)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive hM hZ) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (pullOf (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive hM hZ))) (ZV (groupLayK (At.cs Zp) loFive (stageOf (gsAt
      0) 219) radFull kbFive hM hZ) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive hM hZ).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs
      Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive hM hZ))) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ
      w₀ w₁) (dBat (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).length + nGK Zp cF 0)) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) b.place (XK h 0) (oAt (ixK10 0)) (noFiveAt (At.seats Zp) (At.pseats Zp))
      (h.toAtMg.row L) Q.k)
    (n : ℕ)
    (e : n = nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM
      hZ).length + nGK Zp cF 0)
    (h57 : n ≤ 2 ^ 57) :
    ∃ (lo : List (OracleShape × ℕ)) (gs : GroupSize) (kb : Fin lo.length → Bool) (hM : ∀ i, memMain
      lo i → (lo.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (lo.get i).1 = (stageOf gs 219).C) (hZ : ∀
      i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (lo.get i).1 = (stageOf gs
      219).Z) (keep : (sigOf (At.cs Zp) lo).O → Prop) (_ : DecidablePred keep) (B : Type) (_ :
      Fintype B) (num : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin n)
      (Kc St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) lo).sub ((groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) n num)).kp).Msg × Wp)) (w₀ : (sigOf (At.cs
      Zp) lo).Wit × Wp) (w₁ : LdBrW (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G
      ((groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) n num)).kp Wp) (seat : Fin
      lo.length → ℕ × ℕ) (Nm : SlotNames (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ)) (Lc : List (BatFoldCaller GE)) (smpD : ProofFile.InstPub × TS → (i : Fin lo.length) → Option
      ((sigOf (At.cs Zp) lo).om i).Smp) (σ₀ : (sigOf (At.cs Zp) lo).Smp) (st₀ : St₀) (e₀ : E₀.Str)
      (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ).Sh.par.Cw.nat.Str) (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ).G.A, ((sigOf (At.cs Zp) lo).om a.1).Z.S), ((sigOf (At.cs Zp) lo).om as.1.1).Z.D →
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE) (no : Fin lo.length
      → ℕ), K10Heavy (At.cs Zp) lo gs kb hM hZ keep n num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF)
      seat Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 0)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁) (dBat n) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) b.place (XK h 0) (oAt (ixK10 0)) no (h.toAtMg.row L) Q.k ∧ Q.k = gs.k := by
  subst e
  exact ⟨loFive, gsAt 0, kbFive, hM, hZ, keep, inferInstance, _, inferInstance, (numBy (nPK Zp cF 0)
    (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_nodup
    (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (esOf_all (At.cs Zp) loFive
    (stageOf (gsAt 0) 219) radFull kbFive hM hZ)), Kc, St₀, Wp, E₀, A₀, w₀, w₁, seatFiveAt
    (At.pseats Zp), namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ (noFiveAt
    (At.seats Zp) (At.pseats Zp)), Lc, fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats
          Zp) a ⟨loFive, (seatFiveAt (At.pseats Zp))⟩ i, σ₀, st₀, e₀, mW, pSseed (At.cs Zp) loFive
    (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ) (namesOf (At.cs Zp)
    loFive (stageOf (gsAt 0) 219) radFull kbFive hM hZ (noFiveAt (At.seats Zp) (At.pseats Zp)))
    (stPub loFive (noFiveAt (At.seats Zp) (At.pseats Zp))) L₀ (noFiveAt (At.seats Zp) (At.pseats
    Zp)), noFiveAt (At.seats Zp) (At.pseats Zp), k10_heavy_five_n h L hrr b.place hp hK b Q base hQ
    _ h57 hM hZ keep _ A₀ w₀ w₁ Lc σ₀ st₀ e₀ mW _ (k10_last_of_two _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Car (k10_tie_five h L hrr b.place hp hK
    b Q base hM hZ keep A₀ w₀ w₁ Lc σ₀ st₀ e₀ mW L₀ h0 hA seed)), hQ⟩

open Classical in
/-- **WHAT IS LEFT AT LINK 0: K10Car.** -/
theorem k10_all_five (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      (k10_hM_five h) (k10_hZ_five h)).Sh.par.Cw.nat.Str)
    (Car : ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par) (g0 :
            OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp 0 = some pw →
      ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 0]? = some b → (h.toAtMg.row
                           L)[ixK10 0]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                           (restCap L.e₁ (ixK10 0) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) → b.place.kind =
      KindName.K10 → Q.k = g0.k → g0.k = kLay (linksFullLit.getD 0 []) (kbAt shapeFull 0
      (linksFullLit.getD 0 [])) → (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK
      s).1 (rdK s).2.1 (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) → K10Car (At.cs Zp)
      loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (fun _ => False) (nPK Zp cF 0 + (esOf
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
      h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))) (joint0 (At.cs
      Zp) loFive (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF
      0)) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five
      h) (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))
      (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
      h)))) (wit0 (At.cs Zp) loFive) (brw0 (At.cs Zp) loFive (gsAt 0) kbFive (k10_hM_five h)
      (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0)) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)).length + nGK Zp cF 0)
      (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull
      kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219)
      radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) (F0T OnBytes.secondHashFunction Zp Np cF)
      (seatFiveAt (At.pseats Zp)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      (k10_hM_five h) (k10_hZ_five h) (noFiveAt (At.seats Zp) (At.pseats Zp))) [] (At.smp Zp) (fun
      (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨loFive, (seatFiveAt
            (At.pseats Zp))⟩ i) (smp0 (At.cs Zp) loFive) () () mW (At.arr Zp) (At.ms Zp Z.lay) (dtK
            (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf (pSseed (At.cs Zp)
                        loFive (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
                        (k10_hZ_five h)) (namesOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five
                        h) (k10_hZ_five h) (noFiveAt (At.seats Zp) (At.pseats Zp))) (stPub loFive (noFiveAt (At.seats
                        Zp) (At.pseats Zp))) ((layPub_some (no := noFiveAt (At.seats Zp) (At.pseats Zp))
                        five_layout).choose) (noFiveAt (At.seats Zp) (At.pseats Zp))) Q b base L.e₁ (ixK10 0)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) loFive (stageOf (gsAt 0)
      219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)).foldCaller (fun _ => False) (SbV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
      (k10_hZ_five h)) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0))) (slV (groupLayK (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (pullOf (groupLayK
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) (ZV
      (groupLayK (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
      (k10_hZ_five h)) (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      (k10_hM_five h) (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0)
      (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))
      (esOf_nodup (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
      (k10_hZ_five h)) (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      (k10_hM_five h) (k10_hZ_five h)))) ((1 : Fin 3), (1 : GE)) (joint0 (At.cs Zp) loFive (gsAt 0)
      kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0)) (nPK Zp cF 0 +
      (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
      h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp) loFive (stageOf
      (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup (At.cs Zp) loFive
      (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_all (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)))) (placeFull
      (gsAt 0).k).bC (placeFull (gsAt 0).k).bZ (wit0 (At.cs Zp) loFive) (brw0 (At.cs Zp) loFive
      (gsAt 0) kbFive (k10_hM_five h) (k10_hZ_five h) (Fin (nPK Zp cF 0) ⊕ Fin (nGK Zp cF 0)) (nPK
      Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h)
      (k10_hZ_five h)).length + nGK Zp cF 0) (numBy (nPK Zp cF 0) (nGK Zp cF 0) (esOf (At.cs Zp)
      loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h)) (esOf_nodup
      (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five h))
      (esOf_all (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive (k10_hM_five h) (k10_hZ_five
      h))))) (dBat (nPK Zp cF 0 + (esOf (At.cs Zp) loFive (stageOf (gsAt 0) 219) radFull kbFive
      (k10_hM_five h) (k10_hZ_five h)).length + nGK Zp cF 0)) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 0) b.place (XK h 0) (oAt (ixK10 0))
      (noFiveAt (At.seats Zp) (At.pseats Zp)) (h.toAtMg.row L) Q.k) :
    ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par) (g0 :
            OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp 0 = some pw →
      ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 0]? = some b → (h.toAtMg.row
                           L)[ixK10 0]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                           (restCap L.e₁ (ixK10 0) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) → b.place.kind =
      KindName.K10 → Q.k = g0.k → g0.k = kLay (linksFullLit.getD 0 []) (kbAt shapeFull 0
      (linksFullLit.getD 0 [])) → (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK
      s).1 (rdK s).2.1 (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) → ∃ (lo : List
      (OracleShape × ℕ)) (gs : GroupSize) (kb : Fin lo.length → Bool) (hM : ∀ i, memMain lo i →
      (lo.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (lo.get i).1 = (stageOf gs 219).C) (hZ : ∀ i,
      memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (lo.get i).1 = (stageOf gs 219).Z)
      (keep : (sigOf (At.cs Zp) lo).O → Prop) (_ : DecidablePred keep) (B : Type) (_ : Fintype B)
      (num : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin Q.rows) (Kc
      St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) lo).sub ((groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num)).kp).Msg × Wp)) (w₀ : (sigOf
      (At.cs Zp) lo).Wit × Wp) (w₁ : LdBrW (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ).G ((groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ)))
      (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num)).kp Wp) (seat :
      Fin lo.length → ℕ × ℕ) (Nm : SlotNames (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ)) (Lc : List (BatFoldCaller GE)) (smpD : ProofFile.InstPub × TS → (i : Fin lo.length) → Option
      ((sigOf (At.cs Zp) lo).om i).Smp) (σ₀ : (sigOf (At.cs Zp) lo).Smp) (st₀ : St₀) (e₀ : E₀.Str)
      (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ).Sh.par.Cw.nat.Str) (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ).G.A, ((sigOf (At.cs Zp) lo).om a.1).Z.S), ((sigOf (At.cs Zp) lo).om as.1.1).Z.D →
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE) (no : Fin lo.length
      → ℕ), K10Heavy (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np
      cF) seat Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 0)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 0) b.place (XK h 0) (oAt (ixK10 0)) no (h.toAtMg.row L) Q.k ∧ Q.k = gs.k :=
  fun pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb =>
    k10_exists_five h L hrr b (k10_place_at h _ b hfl) hBK Q base
      (k10_hQ_l 0 (by omega) Q g0 e1 e2) (k10_hM_five h) (k10_hZ_five h) (fun _ => False)
      (joint0 _ _ _ _ _ _ _ _ _) (wit0 _ _) (brw0 _ _ _ _ _ _ _ _ _) [] (smp0 _ _) () () mW _
      (layPub_some five_layout).choose_spec (joint0_on _ _ _ _ _ _ _ _ _)
      (fun _ _ hx i _ => seed_at_five h hx.1 hx.2.1 hx.2.2 i (tie_five_laid h.toAtMg i))
      (Car pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb) Q.rows
      (k10_rows_five h pw b Q h9 hQp hfl hBK _ _) (k10_57_l h 0 (by omega) pw b Q h9 hQp hfl hBK)

end P5J

#print axioms P5J.k10_heavy_five_n
#print axioms P5J.k10_tie_five
#print axioms P5J.k10_exists_five
#print axioms P5J.k10_all_five
