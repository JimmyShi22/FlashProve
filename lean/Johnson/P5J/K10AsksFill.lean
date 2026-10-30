-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10AsksFill.lean: AT THE CLOSED CONSTANT: OF THE 35 PREMISES OF K10's ASSEMBLED LAW
(`K10TwoAsks`, Johnson/Desc/First/Close/Law/K10TwoAsks.lean) EIGHTEEN ARE LAID IN: THIRTEEN BY
CALLS, FIVE OUT OF THIS FILE's THEOREMS' OWN HYPOTHESES; THE OTHER SEVENTEEN ARE `K10Heavy`
(K10Heavy.lean, beside that file). Two statements and their proofs: calls.

  `k10_asks_of_heavy`: at a link l, K10's place p there, the sub-protocol b, the plan's Q, the base:
    `K10Heavy` at the constant's letters gives `K10TwoAsks` there. THIRTEEN FIELDS ARE PAID HERE BY
    CALLS: hcs (`AtMg.codes_full`) · hρ (by definition, at ρ := `realRd ..`) · hrow,
    hMg (`mgAtAll_row`, `mgAtAll_pin`) · hins, hOut, hO, hP (`k10_ins_at`, `k10_out_at`,
    `k10_rows_open_at`, `k10_samples_pins_at`, at O := `oAt (ixK10 l)`) · hB (`smpNamed_bySeat`) ·
    hStay (`k10_smpNamed`) · T1, T2 (`k10_T1_at`, `k10_T2_at`) · hU (from `XK`'s own text). FIVE ARE
    HANDED ON FROM THE THEOREM's OWN HYPOTHESES, NOT PAID HERE: hp, hK (p is the place number `ixK10
    l` of `At.ps`, of the kind K10) · H (Hb: b's yes is the closing's at Q's entries) · hrw (hS: the
    seated row holds the maker's piece at `ixK10 l`) · hk' (hQ: Q.k = gs.k). K10SeatedOfHeavy.lean,
    beside this file, has them out of the hypotheses of `AtMgA.K10Seated` (hp by one more call).
  `k10_piece_of_heavy`: so `K10Heavy` there, under the same hypotheses, gives the sentence of K10's
    debt at that link, by `k10_piece_of_asks`.
Limits. `K10Heavy`'s seventeen stand. Nothing on soundness.

-/
import Johnson.P5J.K10PieceOfAsks
import Johnson.P5J.K10KeptTests
import Johnson.P5J.CodesFullAtMg
import Johnson.Desc.First.Close.Law.K10Heavy

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

/-- **EIGHTEEN OF THE 35 ARE LAID IN: THIRTEEN BY CALLS, FIVE OUT OF THE HYPOTHESES.** -/
theorem k10_asks_of_heavy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (l : ℕ)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 l]? = some p)
    (hK : p.kind = KindName.K10) (b : Block TS ProofFile.Cl) (Q : Par) (base : ℕ)
    (hS : (h.toAtMg.row L)[ixK10 l]? =
      some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))))
    (Hb : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2)
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
    (smpD : ProofFile.InstPub × TS → (i : Fin lo.length) → Option ((sigOf (At.cs Zp) lo).om i).Smp)
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
      seat Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 :
      Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) (oAt
      (ixK10 l)) no (h.toAtMg.row L) Q.k)
    (hQ : Q.k = gs.k) :
    K10TwoAsks (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF) seat
      Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 :
      Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) (oAt
      (ixK10 l)) no (h.toAtMg.row L) Q.k :=
  { hcs := h.toAtMg.codes_full
    hen := A.hen
    hgs := A.hgs
    hC := A.hC
    hV := A.hV
    hPr := A.hPr
    hρ := rfl
    H := Hb
    hn57 := A.hn57
    hp := hp
    hK := hK
    hrow := mgAtAll_row h
    hMg := mgAtAll_pin h
    hins := k10_ins_at (ixK10 l) p hp hK
    hOut := k10_out_at (ixK10 l) p hp hK
    hO := k10_rows_open_at (ixK10 l) p hp hK
    hP := k10_samples_pins_at (ixK10 l) p hp hK
    hSit := A.hSit
    hAl := A.hAl
    hB := smpNamed_bySeat (At.cs Zp) (At.seats Zp)
    hStay := fun z _ _ hs y i => k10_smpNamed (At.cs Zp) (At.seats Zp) z hs y i
    hHit := A.hHit
    hAlM := A.hAlM
    hGrp := A.hGrp
    hi1 := A.hi1
    hi2 := A.hi2
    T1 := k10_T1_at h.toAtMg (ixK10 l) p hp hK
    T2 := k10_T2_at h L q1 q2 q3 (ixK10 l) p hp hK _ hS
    hU := fun _ hx => Classical.not_not.1 hx.2.2
    hX := A.hX
    hCfX := A.hCfX
    hCar := A.hCar
    hk' := hQ
    hrw := hS
    hOn := A.hOn }

/-- **SO THE SEVENTEEN GIVE THE SENTENCE OF K10's DEBT AT THE LINK.** -/
theorem k10_piece_of_heavy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (l : ℕ)
    (p : VerifiableInference.Desc.Place) (hp : At.ps[ixK10 l]? = some p)
    (hK : p.kind = KindName.K10) (b : Block TS ProofFile.Cl) (Q : Par) (base : ℕ)
    (hS : (h.toAtMg.row L)[ixK10 l]? =
      some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))))
    (Hb : ∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2)
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
    (smpD : ProofFile.InstPub × TS → (i : Fin lo.length) → Option ((sigOf (At.cs Zp) lo).om i).Smp)
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
      seat Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
      (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ).foldCaller keep (SbV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 :
      Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
      (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
      id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) (oAt
      (ixK10 l)) no (h.toAtMg.row L) Q.k)
    (hQ : Q.k = gs.k) :
    ∃ o : ST → Prop,
      ((pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo)) : PC).withMap
        (h.toAtMg.ex L (ixK10 l))).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (insQ fullLinks At.ps (ixK10 l)))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps (ixK10 l))) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) s →
        h.toAtMg.rch (ixK10 l) s → ¬ s.1.2.failed ≠ none → o s :=
  k10_piece_of_asks h L l b Q base lo gs kb hM hZ keep num A₀ w₀ w₁ seat Nm Lc smpD σ₀ st₀ e₀ mW pS
    _ p _ no _ _
    (k10_asks_of_heavy h L q1 q2 q3 l p hp hK b Q base hS Hb lo gs kb hM hZ keep num A₀ w₀ w₁ seat
      Nm Lc smpD σ₀ st₀ e₀ mW pS no A hQ) hQ

end P5J

#print axioms P5J.k10_asks_of_heavy
#print axioms P5J.k10_piece_of_heavy
