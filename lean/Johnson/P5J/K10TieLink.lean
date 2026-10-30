-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10TieLink.lean: AT THE CLOSED CONSTANT, AT A LINK l WITH 1 ≤ l < 25: THE FIRST TIE OF
K10's LAW (`K10FirstTie`: the field hOn of `K10Heavy`; Johnson/Desc/First/Close/Law/K10LastTwo.lean)
BY SEVERAL THEOREMS, UNDER ONE PREMISE ON THE STATE: seed. Two definitions, a statement and
its proof: calls.

  `nPK Zp cF l`, `nGK Zp cF l`: the numbers of plain rows and of generator rows that the table's
    numbers count at K10's border of link l (`plainDue`, `gensDue`).
  THE LINK's LETTERS, beside those of K10HeavyLink.lean: B := Fin nPK ⊕ Fin nGK · n := nPK + the
    members' samples' number + nGK · num := `numBy ..` · pS := `pSseed .. (stPub lo no) L₀ no`, L₀
    what `layPub` returns. The joint beside A₀ stays a letter with its promise at (st₀, e₀) a
    hypothesis.
  `k10_tie_link`: `K10FirstTie` there. By `onS_of_rowAsks`, its premises laid in: the
    row asks (`AtMgA.hX_paid`) · front (`fa_front_same` with `k10_hV_at`, `k10_hCfX_at`) · the five
    numbers (`five_of_facts`) · hm, hc (`hm_at`, `covered_laid`) · good (`good_cs`) · agrees
    (`linksFull_layout`) · kL, h0 (`kh_at`) · apart (`AtMg.hinge_inj`) · tie (`tie_at_laid`) · plan
    (`plan_of_shapes` at the begun statement, from the hinge `AtMg.hinge_all`). LEFT AS A
    HYPOTHESIS: seed: under `XK h l`: at every member of the list the statement holds the seed of
    its sample (`K1.SeedIs`).
Limits. seed stands; so do `rowsRead Z`, the plan's list with `FoldFacts`, and hM, hZ. Link 0 is not
here. Nothing on soundness.

-/
import Johnson.P5J.K10LinkFacts
import Johnson.LPFE1R.RowsDueAt
import Johnson.LPFE1R.K10Small
import Johnson.Desc.First.Link.Law.OnOfRowAsks
import Johnson.Desc.First.Close.Law.PlanOfShapes
import Johnson.Desc.First.Close.Law.StageClosed
import Johnson.Desc.First.Close.Law.K10LastTwo

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
open VerifiableInference.Desc.First.Close (K10FirstTie namesOf noK10 seatK10 written_of_mem
  linksFull_layout onS_of_rowAsks fa_front_same good_cs
  plan_of_shapes stPub layPub begun_at shapesAre_begun)
open VerifiableInference.Desc.LinkJoin (loAt kbW gsAt tie_at_laid smpDrawn covered_laid hm_at
  plainDue gensDue numBy esOf esOf_nodup esOf_all pSseed)
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

/-- The plain rows that the table's numbers count at K10's border of link l. -/
abbrev nPK (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (l : ℕ) : ℕ :=
  plainDue (At.N Zp cF) (oAt (ixK10 l)) l

/-- The generator rows that they count there. -/
abbrev nGK (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (l : ℕ) : ℕ :=
  gensDue (At.N Zp cF) (oAt (ixK10 l)) l

open Classical in
/-- **THE FIRST TIE AT A LINK FROM 1 TO 24, UNDER seed.** -/
theorem k10_tie_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (h1 : 1 ≤ l) (hl : l < 25) (p : VerifiableInference.Desc.Place)
    (hp : At.ps[ixK10 l]? = some p) (hK : p.kind = KindName.K10) (b : Block TS ProofFile.Cl) (Q : Par)
    (base : ℕ)
    (hM : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.mainRows ≠ 0 → cMain (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).C)
    (hZ : ∀ i, memMain (loAt l) i → ((loAt l).get i).1.maskRows ≠ 0 → cMask (At.cs Zp) ((loAt l).get
      i).1 = (stageOf (gsAt l) 219).Z)
    (keep : (sigOf (At.cs Zp) (loAt l)).O → Prop)
    [DecidablePred keep]
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) (loAt l)).sub ((groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) hM hZ) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l))) (slV (groupLayK
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (pullOf (groupLayK (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt
      l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK
      Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (esOf_nodup
      (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (esOf_all (At.cs Zp) (loAt
      l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)))).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) (loAt l)).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).G
      ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (Fin (nPK Zp cF
      l) ⊕ Fin (nGK Zp cF l))) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (nPK
      Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length + nGK
      Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      hM hZ) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)))).kp Wp)
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) (loAt l)).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW
      l) hM hZ).Sh.par.Cw.nat.Str)
    (L₀ : GroupLayout)
    (h0 : layPub (loAt l) (kbW l) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) = some L₀)
    (hA : A₀.on (st₀, e₀))
    (seed : ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) → ∀ i : Fin (loAt l).length,
      memMain (loAt l) i → ∃ (ρ : (Fin (bitsZ (At.cs Zp) ((loAt l).get i).1) → GE) × Units GE) (y :
      GE),
      VerifiableInference.Desc.K1.SeedIs (At.cs Zp) ((loAt l).get i).1 a.1.st (noK10 (At.seats Zp)
      (loAt l) (At.pseats Zp) l i) ρ y) :
    K10FirstTie (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep (nPK Zp cF l + (esOf (At.cs Zp)
      (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length + nGK Zp cF l) (numBy (nPK Zp cF
      l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
      (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (esOf_all (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)) A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np
      cF) (seatK10 (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) Lc (At.smp Zp) (fun (a
      : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l), (seatK10 (loAt l)
            (At.pseats Zp) l)⟩ i) σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction
            Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf (pSseed (At.cs Zp) (loAt l) (groupLayK (At.cs
            Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (namesOf (At.cs Zp) (loAt l)
            (stageOf (gsAt l) 219) radFull (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l))
            (stPub (loAt l) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) L₀ (noK10 (At.seats Zp) (loAt
            l) (At.pseats Zp) l)) Q b base L.e₁ (ixK10 l) (VerifiableInference.Desc.First.Close.realRd
            ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).foldCaller keep
            (SbV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (Fin (nPK Zp
            cF l) ⊕ Fin (nGK Zp cF l))) (slV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
            (kbW l) hM hZ) (pullOf (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
            hM hZ))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (nPK
            Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length + nGK
            Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
            radFull (kbW l) hM hZ) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
            hM hZ) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ))) ((1 : Fin
            3), (1 : GE)) A₀ (placeFull (gsAt l).k).bC (placeFull (gsAt l).k).bZ w₀ w₁) (dBat (nPK Zp cF l
            + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ).length + nGK Zp cF
            l)) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
            (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 l) p (XK h l) (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)
      (h.toAtMg.row L) Q.k := by
  refine ⟨fun z a hx => ?_⟩
  exact onS_of_rowAsks (Pr := Q) (z := z) (a := a) (Nu := At.N Zp cF) (O := oAt (ixK10 l)) (m := l)
    (hX := k10_hX_l h Ld hLd Fo l hl p hp hM hZ z a hx) (hP := rfl) (hN := rfl)
    (front := fa_front_same (hV := k10_hV_at Zp (loAt l) _ fun i => tie_at_laid h.toAtMg hl i)
      (z := z) (a := a) (hc := k10_hCfX_at h l (loAt l) _ (k10_sits_l h hrr l h1 hl p hp hK) z a hx)
      (hA := hA) ..)
    (five := k10_five_l h Ld Fo l hl p hp hM hZ Q z a hx) (hm := hm_at hl)
    (hc := covered_laid h.scope h.laid hl)
    (good := good_cs (At.cs Zp) h.toAtMg.codes_full (loAt l) (written_of_mem (loAt_mem l hl))
      (gsAt l) (gsAt_ok l hl).1 (kbW l) hM hZ (k10_corners_l l hl))
    (agrees := linksFull_layout _ (loAt_mem l hl) _) (kL := (kh_at l hl).1) (h0 := (kh_at l hl).2)
    (apart := h.toAtMg.hinge_inj l (by omega)) (tie := fun i _ => tie_at_laid h.toAtMg hl i)
    (seed := seed z a hx)
    (plan := fun Gr lay hG hlay as D => plan_of_shapes (At.cs Zp) (stageOf (gsAt l) 219) radFull hM
      hZ _ h0 (begun_at _ Gr hG) hlay
      (shapesAre_begun _ (h.toAtMg.hinge_all Fo rfl hl ((z, a.1), a.2) hx.2.1
        (not_not.1 hx.2.2) Gr hG)) as D) ..

end P5J

#print axioms P5J.k10_tie_link
