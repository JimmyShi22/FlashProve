-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10VCfAt.lean: AT THE CLOSED CONSTANT: TWO OF THE SEVEN HEAVY PREMISES OF K10's LAW
(`K10Heavy`, Johnson/Desc/First/Close/Law/K10Heavy.lean): hV AND hCfX, BY OTHER FILES' TWO
THEOREMS; EACH UNDER ONE PREMISE. Three statements and their proofs: the two terms are theirs.

  `k10_hV_at`: hV at smpD := the drawn reader (`smpDrawn`,
    Johnson/Desc/First/Link/Law/DrawnSeed.lean) and smpS := `At.smp Zp`: by `sameVal_drawn`. UNDER
    hT: `K1.Tie (At.cs Zp) (lo.get i).1` at every message of the list.
  `k10_hCfX_at`: hCfX at X := `XK h l`: by `cf_of_promise` (FrontAtK10.lean, beside that file), from
    the promise and "no mark" in `XK`. UNDER hM: `SitsIn` at the constant's data, `At.N Zp cF`, `oAt
    (ixK10 l)`, lo, seat: at every message of the list: a member of the constant's members is alike
    to it, and its seat is among the sampled tenants whose pin is open at K10's border.
  `k10_heavy_VCf`: A TEST OF THE TWO TEXTS: the two statements are laid in the places of
    `K10Heavy`'s fields hV and hCfX at the constant's letters: so Lean holds that they are these
    fields, to the letter.
General in the list lo and the seats: they serve the written lists and link 0's five-list.
Limits. hT and hM stand. Nothing on soundness.

-/
import Johnson.P5J.K10AsksFill
import Johnson.Desc.First.Link.Law.FrontAtK10
import Johnson.Desc.First.Link.Law.DrawnSeed

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.LinkJoin (sameVal_drawn smpDrawn cf_of_promise SitsIn)
open VerifiableInference.Desc.First.Close (SameVal)

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

/-- **hV AT THE CONSTANT.** -/
theorem k10_hV_at (Zp : ProofFile.Pub) (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
    (hT : ∀ i, VerifiableInference.Desc.K1.Tie (At.cs Zp) (lo.get i).1) :
    SameVal (At.cs Zp) lo
      (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨lo, seat⟩ i)
      fun q j => At.smp Zp q ⟨lo, seat⟩ j :=
  fun a i zz hz => sameVal_drawn (At.cs Zp) (At.seats Zp) a ⟨lo, seat⟩ i (hT i) zz hz

/-- **hCfX AT THE CONSTANT.** -/
theorem k10_hCfX_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ)
    (lo : List (OracleShape × ℕ)) (seat : Fin lo.length → ℕ × ℕ)
    (hM : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) lo seat) :
    ∀ z (a : TS × (Frame.E FR).Str), XK h l ((z, a.1), a.2) →
      ∀ i, CfAt (F0T OnBytes.secondHashFunction Zp Np cF) (At.cs Zp) lo seat
        (fun q => At.smp Zp q ⟨lo, seat⟩) i (z, a.1) (strsOf FR a.2) :=
  fun z a hx i => cf_of_promise (𝔇 := h.𝔇) (Mg := mgBase) (At.N Zp cF) fullLinks At.ps (ixK10 l)
    ((z, a.1), a.2) hx.1 (Classical.not_not.1 hx.2.2) lo seat hM
    (smpNamed_bySeat (At.cs Zp) (At.seats Zp)) i

/-- **THE TWO STATEMENTS ARE K10Heavy's FIELDS hV AND hCfX AT THE CONSTANT's LETTERS**: they can be
laid in their places. (A test of the two texts: it adds nothing to what is known.) -/
theorem k10_heavy_VCf (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (l : ℕ)
    (p : VerifiableInference.Desc.Place) (b : Block TS ProofFile.Cl) (Q : Par) (base : ℕ)
    (lo : List (OracleShape × ℕ))
    (gs : GroupSize)
    (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (lo.get i).1 = (stageOf
      gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (lo.get i).1 = (stageOf
      gs 219).Z)
    (keep : (sigOf (At.cs Zp) lo).O → Prop)
    [DecidablePred keep]
    {B : Type}
    [Fintype B]
    (num : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin Q.rows)
    {Kc St₀ Wp : Type}
    {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) lo).sub ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ)
      B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ) Q.rows num)).kp).Msg × Wp))
    (w₀ : (sigOf (At.cs Zp) lo).Wit × Wp)
    (w₁ : LdBrW (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G ((groupLayK (At.cs Zp)
      lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ)
      (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num)).kp Wp)
    (seat : Fin lo.length → ℕ × ℕ)
    (Nm : SlotNames (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))
    (Lc : List (BatFoldCaller GE))
    (σ₀ : (sigOf (At.cs Zp) lo).Smp)
    (st₀ : St₀)
    (e₀ : E₀.Str)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ).Sh.par.Cw.nat.Str)
    (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G.A, ((sigOf
      (At.cs Zp) lo).om a.1).Z.S), ((sigOf (At.cs Zp) lo).om as.1.1).Z.D → (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE)
    (no : Fin lo.length → ℕ)
    (A : K10Heavy (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF)
      seat Nm Lc (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a
      ⟨lo, seat⟩ i) σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np
      cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀
      (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id))
      (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) (oAt (ixK10 l)) no (h.toAtMg.row
      L) Q.k)
    (hT : ∀ i, VerifiableInference.Desc.K1.Tie (At.cs Zp) (lo.get i).1)
    (hM' : SitsIn h.𝔇 (At.N Zp cF) (oAt (ixK10 l)) lo seat) :
    K10Heavy (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF) seat
      Nm Lc (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨lo,
            seat⟩ i) σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF
            h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp)
      lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf
      gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ)
      (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull
      gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp
      cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) (oAt (ixK10 l)) no (h.toAtMg.row L) Q.k
      :=
  { A with
    hV := k10_hV_at Zp lo seat hT
    hCfX := k10_hCfX_at h l lo seat hM' }

end P5J

#print axioms P5J.k10_hV_at
#print axioms P5J.k10_hCfX_at
#print axioms P5J.k10_heavy_VCf
