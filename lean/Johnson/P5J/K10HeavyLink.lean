-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10HeavyLink.lean: AT THE CLOSED CONSTANT, AT A LINK l WITH 1 ≤ l < 25: OF THE SEVENTEEN
PREMISES `K10Heavy` (Johnson/Desc/First/Close/Law/K10Heavy.lean) FOURTEEN ARE LAID IN BY SEVERAL
THEOREMS AND ONE IS HANDED ON FROM A HYPOTHESIS; THE OTHER TWO ARE `K10Last` (K10Last.lean,
beside that file). A statement and its proof: calls.

Why. Each of the fourteen has a theorem that fits it by report. This file is Lean's
word that they fit: at one choice of the letters, together.
  THE LINK's LETTERS: lo := `loAt l` (the written list) · gs := `gsAt l` (the written table's row's
    group in front) · kb := `kbW l` · seat := `seatK10 (loAt l) (At.pseats Zp) l` · no := `noK10
    (At.seats Zp) (loAt l) (At.pseats Zp) l` · Nm := `namesOf .. no` · smpD := the drawn reader
    (`smpDrawn`). The other typed letters stay letters.
  `k10_heavy_link`: `K10Last` there gives `K10Heavy` there. FOURTEEN LAID IN: hen (`written_of_mem`,
    `loAt_mem`) · hgs, and gs.k for hC (`gsAt_front`: the kernel's) · hC (`linksFull_corners_all`) ·
    hV (`k10_hV_at` with `tie_at_laid`) · hPr (`hPr_of`) · hSit, hAl, hHit, hAlM, hGrp, hi1, hi2
    (`plan_seven_at`) · hX (`AtMgA.hX_paid`) · hCfX (`k10_hCfX_at` with `sitsIn_at`). ONE HANDED ON
    FROM THE THEOREM's OWN HYPOTHESIS, NOT PAID HERE: hn57 (h57).
  ITS HYPOTHESES BESIDE THE HEAD: `rowsRead Z` (the goals' one named condition) · the plan's list Ld
    with `laidAtCodes .. = some Ld` and `FoldFacts` at "reached" over it · K10's place p at `ixK10
    l` · Q.k = (gsAt l).k · Q.rows ≤ 2 ^ 57.
Limits. `K10Last`'s two stand. Link 0 is not here (its list is the five-list). Nothing on soundness.

-/
import Johnson.P5J.K10VCfAt
import Johnson.P5J.K10SeatsAt
import Johnson.LPFE1R.PlanSevenAt
import Johnson.LPFE1R.SitsInAt
import Johnson.LPFE1R.TieAtLists
import Johnson.Desc.First.Close.Law.HPrOf
import Johnson.Desc.First.Close.Law.K10Last

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item FoldFacts)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (K10Last namesOf noK10 seatK10 written_of_mem
  linksFull_corners_all hPr_of)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt gsAt_front plan_seven_at sitsIn_at tie_at_laid
  smpDrawn)
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

/-- **FOURTEEN OF THE SEVENTEEN BY THEOREMS, ONE HANDED ON, AT A LINK FROM 1 TO 24.** -/
theorem k10_heavy_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (h1 : 1 ≤ l) (hl : l < 25) (p : VerifiableInference.Desc.Place)
    (hp : At.ps[ixK10 l]? = some p) (hK : p.kind = KindName.K10) (b : Block TS ProofFile.Cl) (Q : Par)
    (base : ℕ) (hQ : Q.k = (gsAt l).k) (h57 : Q.rows ≤ 2 ^ 57)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).Z)
    (keep : (sigOf (At.cs Zp) (loAt l)).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (num : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G.Row B ≃
      Fin Q.rows)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) Q.rows num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) (loAt l)).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G
      ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) B) (slV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) Q.rows num)).kp Wp)
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) (loAt l)).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW
      l) hM hZ).Sh.par.Cw.nat.Str)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).G.A, ((sigOf (At.cs Zp) (loAt l)).om a.1).Z.S), ((sigOf (At.cs Zp) (loAt l)).om
      as.1.1).Z.D → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).Sh.Cin.J → GE)
    (A : K10Last (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep Q.rows num A₀ w₀ w₁ (F0T
      OnBytes.secondHashFunction Zp Np cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l)
                  (stageOf (gsAt l) 219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
      Lc (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l),
            (seatK10 (loAt l) (At.pseats Zp) l)⟩ i) σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt
            Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ
      w₀ w₁) (dBat Q.rows) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 l) p (XK h l) (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)
      (h.toAtMg.row L) Q.k) :
    K10Heavy (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction
      Zp Np cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) Lc (At.smp Zp)
      (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l), (seatK10 (loAt
            l) (At.pseats Zp) l)⟩ i) σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
            OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) hM hZ) B) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ
      w₀ w₁) (dBat Q.rows) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 l) p (XK h l) (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)
      (h.toAtMg.row L) Q.k := by
  have hpl : p.link.getD 0 = l := by
    rw [(k10_place l hl p hp).1]
    rfl
  have g := List.all_eq_true.1 gsAt_front l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at g
  have PS := plan_seven_at h.scope h.laid hrr hp hK (by rw [hpl]; exact hl)
  have SI := sitsIn_at h hrr hp hK (by rw [hpl]; exact h1) (by rw [hpl]; exact hl)
  rw [hpl] at PS SI
  exact
    { hen := written_of_mem (loAt_mem l hl)
      hgs := g.1
      hC := by
        rw [g.2]
        exact linksFull_corners_all _ (loAt_mem l hl) _
      hV := k10_hV_at Zp (loAt l) _ fun i => tie_at_laid h.toAtMg hl i
      hPr := hPr_of (At.cs Zp) (loAt l) (gsAt l) g.1 (kbW l) hM hZ Q hQ
      hn57 := h57
      hSit := PS.hSit
      hAl := PS.hAl
      hHit := PS.hHit
      hAlM := PS.hAlM
      hGrp := PS.hGrp
      hi1 := PS.hi1
      hi2 := PS.hi2
      hX := h.hX_paid Ld hLd Fo l hl p hp hM hZ
      hCfX := k10_hCfX_at h l (loAt l) _ SI
      hCar := A.hCar
      hOn := A.hOn }

end P5J

#print axioms P5J.k10_heavy_link
