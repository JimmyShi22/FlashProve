-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10ExistsLink.lean: AT THE CLOSED CONSTANT, AT A LINK l WITH 1 ≤ l < 25: THE TYPED
LETTERS ARE EXHIBITED: the existence that `AtMgA.K10HeavyAll` (K10SeatedOfHeavy.lean, beside this
file) asks at a link, at a letter n that equals the sum of the three counts. A statement and its
proof: calls.

Why. `K10HeavyAll` says: there are a type B of plain rows and a numbering of the typed group's rows
by Fin Q.rows, and the other letters, with `K10Heavy`. Here they are
terms: B := Fin nPK ⊕ Fin nGK, num := `numBy ..`, and so on. The numbering is by Fin (nPK + the
members' samples' number + nGK): so the statement stands at a letter n with e : n = that sum;
whoever calls it at n := Q.rows owes e (`k10_rows_due` with `esOf_length`).
  `k10_exists_link`: from `K10Car` (what stands behind the closing) at these terms, seed, and the
    hypotheses of K10HeavyLinkN.lean and K10TieLink.lean: the existence. By `k10_heavy_link_n`,
    `k10_last_of_two`, `k10_tie_link`.
Limits. `K10Car` and seed stand. Link 0 is not here. Nothing on soundness.

-/
import Johnson.P5J.K10TieLink
import Johnson.P5J.K10HeavyLinkN

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
/-- **THE TYPED LETTERS, EXHIBITED, AT A LINK FROM 1 TO 24.** -/
theorem k10_exists_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z) (Ld : Laid)
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (l : ℕ) (h1 : 1 ≤ l) (hl : l < 25) (b : Block TS ProofFile.Cl)
    (hp : At.ps[ixK10 l]? = some b.place) (hK : b.place.kind = KindName.K10) (Q : Par)
    (base : ℕ) (hQ : Q.k = (gsAt l).k)
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
      (loAt l) (At.pseats Zp) l i) ρ y)
    (Car : K10Car (At.cs Zp) (loAt l) (gsAt l) (kbW l) hM hZ keep (nPK Zp cF l + (esOf (At.cs Zp)
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
      (ixK10 l) b.place (XK h l) (oAt (ixK10 l)) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)
      (h.toAtMg.row L) Q.k)
    (n : ℕ)
    (e : n = nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM
      hZ).length + nGK Zp cF l)
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
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) n num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁) (dBat n) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 l) b.place (XK h l) (oAt (ixK10 l)) no (h.toAtMg.row L) Q.k ∧ Q.k = gs.k := by
  subst e
  exact ⟨loAt l, gsAt l, kbW l, hM, hZ, keep, inferInstance, _, inferInstance, (numBy (nPK Zp cF l)
    (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)
    (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ) (esOf_all (At.cs
    Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ)), Kc, St₀, Wp, E₀, A₀, w₀, w₁,
    seatK10 (loAt l) (At.pseats Zp) l, namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
    (kbW l) hM hZ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l), Lc, fun (a : ProofFile.InstPub × TS) i
    => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l), (seatK10 (loAt l) (At.pseats Zp) l)⟩ i, σ₀,
    st₀, e₀, mW, pSseed (At.cs Zp) (loAt l) (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
    radFull (kbW l) hM hZ) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) hM hZ
    (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) (stPub (loAt l) (noK10 (At.seats Zp) (loAt l)
    (At.pseats Zp) l)) L₀ (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l), noK10 (At.seats Zp) (loAt
    l) (At.pseats Zp) l, k10_heavy_link_n h L hrr Ld hLd Fo l h1 hl b.place hp hK b Q base hQ _ h57
    hM hZ keep _ A₀ w₀ w₁ Lc σ₀ st₀ e₀ mW _ (k10_last_of_two _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Car (k10_tie_link h L hrr Ld hLd Fo l h1 hl
    b.place hp hK b Q base hM hZ keep A₀ w₀ w₁ Lc σ₀ st₀ e₀ mW L₀ h0 hA seed)), hQ⟩

end P5J

#print axioms P5J.k10_exists_link
