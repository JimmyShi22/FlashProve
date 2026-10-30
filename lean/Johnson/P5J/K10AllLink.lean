-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10AllLink.lean: AT THE CLOSED CONSTANT, AT A LINK l WITH 1 ≤ l < 25: WHAT
`AtMgA.K10HeavyAll` (K10SeatedOfHeavy.lean, beside this file) ASKS AT THAT LINK, FROM THE HEAD,
`rowsRead Z` AND ONE DEBT: `K10Car` (what stands behind the closing). A statement and its proof: one
term of calls.

  THE FREE LETTERS ARE CHOSEN (Johnson/Desc/First/Close/Law/K10Defaults.lean): nothing is kept
    beside (keep := nobody) · the joint beside is the trivial one (`joint0`) · the two default
    witnesses and the default sample are `wit0`, `brw0`, `smp0` (by choice) · the callers' list is
    empty · hM, hZ := `k10_hM_l`, `k10_hZ_l` · L₀ := what `layPub` returns (`layPub_some`, by
    choice). The fresh mask's word mW stays a letter: whoever pays `K10Car` names it.
  `k10_all_link`: if `K10Car` holds at these terms at every b, Q, base with the debt's own
    hypotheses, then at every such b, Q, base THERE ARE the typed letters with `K10Heavy` at n :=
    Q.rows and Q.k = gs.k. LAID IN: `k10_exists_link` · the place (`k10_place_at`) · Q.k
    (`k10_hQ_l`) · Q.rows is the sum of the three counts (`k10_rows_l`) · Q.rows ≤ 2 ^ 57
    (`k10_57_l`) · the plan's list and `FoldFacts` (`atMgR_rch_of_head`, by choice)
    · seed (`seed_at_K10` with `tie_at_laid`).
Limits. `K10Car` stands; so does `rowsRead Z`, which is no part of the head. Link 0 is not here.
Nothing is shown of any state. Nothing on soundness.

-/
import Johnson.P5J.K10SeatedFacts
import Johnson.P5J.StartAtHead
import Johnson.P2LawR.SeedAtK10
import Johnson.Desc.First.Close.Law.K10Defaults

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
/-- **WHAT IS LEFT AT A LINK FROM 1 TO 24: K10Car.** -/
theorem k10_all_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (hrr : rowsRead Z) (l : ℕ)
    (h1 : 1 ≤ l) (hl : l < 25)
    (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW
      l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).Sh.par.Cw.nat.Str)
    (Car : ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par) (g0 :
            OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp l = some pw →
      ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 l]? = some b → (h.toAtMg.row
                           L)[ixK10 l]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                           (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) → b.place.kind =
      KindName.K10 → Q.k = g0.k → g0.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l
      (linksFullLit.getD l [])) → (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK
      s).1 (rdK s).2.1 (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) → K10Car (At.cs Zp)
      (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (fun _ => False) (nPK Zp cF l +
      (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h
      l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl))
      (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
      (k10_hZ_l h l hl))) (joint0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h
      l hl) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF
      l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull
      (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (wit0 (At.cs Zp)
      (loAt l)) (brw0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (Fin
      (nPK Zp cF l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp
      cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l
      h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW
      l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (F0T OnBytes.secondHashFunction Zp Np cF) (seatK10
                  (loAt l) (At.pseats Zp) l) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
                  (k10_hM_l h l hl) (k10_hZ_l h l hl) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) []
      (At.smp Zp) (fun (a : ProofFile.InstPub × TS) i => smpDrawn (At.cs Zp) (At.seats Zp) a ⟨(loAt l),
            (seatK10 (loAt l) (At.pseats Zp) l)⟩ i) (smp0 (At.cs Zp) (loAt l)) () () mW (At.arr Zp) (At.ms
            Zp Z.lay) (dtK (At.EAt Z) OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf (pSseed
                        (At.cs Zp) (loAt l) (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
                        (k10_hM_l h l hl) (k10_hZ_l h l hl)) (namesOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
                        radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (noK10 (At.seats Zp) (loAt l) (At.pseats
                        Zp) l)) (stPub (loAt l) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) ((layPub_some (no :=
                        noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) (linksFull_layout (loAt l) (loAt_mem l hl) (kbW
                        l))).choose) (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l)) Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l)
      219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).foldCaller (fun _ => False) (SbV
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
      (k10_hZ_l h l hl)) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l))) (slV (groupLayK (At.cs Zp) (loAt
      l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (pullOf
      (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
      (k10_hZ_l h l hl)))) (ZV (groupLayK (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      (k10_hM_l h l hl) (k10_hZ_l h l hl)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt
      l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK
      Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l)
      (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf
      (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) ((1 : Fin 3), (1 : GE))
      (joint0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl) (Fin (nPK Zp
      cF l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l) (numBy (nPK Zp cF
      l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h
      l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW
      l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)))) (placeFull (gsAt l).k).bC (placeFull
      (gsAt l).k).bZ (wit0 (At.cs Zp) (loAt l)) (brw0 (At.cs Zp) (loAt l) (gsAt l) (kbW l) (k10_hM_l
      h l hl) (k10_hZ_l h l hl) (Fin (nPK Zp cF l) ⊕ Fin (nGK Zp cF l)) (nPK Zp cF l + (esOf (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l
      hl)).length + nGK Zp cF l) (numBy (nPK Zp cF l) (nGK Zp cF l) (esOf (At.cs Zp) (loAt l)
      (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)) (esOf_nodup (At.cs
      Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl))
      (esOf_all (At.cs Zp) (loAt l) (stageOf (gsAt l) 219) radFull (kbW l) (k10_hM_l h l hl)
      (k10_hZ_l h l hl))))) (dBat (nPK Zp cF l + (esOf (At.cs Zp) (loAt l) (stageOf (gsAt l) 219)
      radFull (kbW l) (k10_hM_l h l hl) (k10_hZ_l h l hl)).length + nGK Zp cF l)) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) b.place (XK h l) (oAt (ixK10 l))
      (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l) (h.toAtMg.row L) Q.k) :
    ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par) (g0 :
            OnBytes.Params.GroupSize), g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp l = some pw →
      ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 l]? = some b → (h.toAtMg.row
                           L)[ixK10 l]? = some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
                           (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) → b.place.kind =
      KindName.K10 → Q.k = g0.k → g0.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l
      (linksFullLit.getD l [])) → (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK
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
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM
      hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK
      (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs
      219) radFull kb hM hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull
      gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo (VerifiableInference.Desc.First.Close.oneOf id)
      (VerifiableInference.Desc.First.Close.oneOf id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps
      (ixK10 l) b.place (XK h l) (oAt (ixK10 l)) no (h.toAtMg.row L) Q.k ∧ Q.k = gs.k :=
  fun pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb =>
    k10_exists_link h L hrr (atMgR_rch_of_head h).choose (atMgR_rch_of_head h).choose_spec.listed
      (atMgR_rch_of_head h).choose_spec.fold l h1 hl b (k10_place_at h _ b hfl) hBK Q base
      (k10_hQ_l l hl Q g0 e1 e2) (k10_hM_l h l hl) (k10_hZ_l h l hl) (fun _ => False)
      (joint0 _ _ _ _ _ _ _ _ _) (wit0 _ _) (brw0 _ _ _ _ _ _ _ _ _) [] (smp0 _ _) () () mW _
      (layPub_some (linksFull_layout (loAt l) (loAt_mem l hl) (kbW l))).choose_spec
      (joint0_on _ _ _ _ _ _ _ _ _)
      (fun _ _ hx i _ => seed_at_K10 h hl hx.1 hx.2.1 hx.2.2 i (tie_at_laid h.toAtMg hl i))
      (Car pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb) Q.rows
      (k10_rows_l h l hl pw b Q h9 hQp hfl hBK _ _) (k10_57_l h l hl pw b Q h9 hQp hfl hBK)

end P5J

#print axioms P5J.k10_all_link
