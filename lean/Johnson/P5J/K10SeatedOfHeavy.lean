-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10SeatedOfHeavy.lean: AT THE CLOSED CONSTANT: K10's DEBT (`AtMgA.K10Seated`,
K10LawSeated.lean, beside this file) FROM A CHOICE OF THE TYPED LETTERS AND THE SEVENTEEN PREMISES
`K10Heavy` AT EVERY LINK. So the field of the kind K10 from the reading law and that. A definition,
statements and proofs: calls.

  `k10_place_at`: the place of the sub-protocol number i of the first chain is number i of `At.ps`
    (`At.places_paid`): this has `k10_asks_of_heavy`'s hp out of `K10Seated`'s hypothesis
    "cF.blocksInOrder[ixK10 l]? = some b".
  `AtMgA.K10HeavyAll h L`: WHAT IS LEFT OF K10's OWN DEBT, WHOLE: at every link l below 25, under
    `K10Seated`'s own hypotheses on pw, b, Q, base (all out of `k10_row_at`): THERE
    ARE the typed letters (the list lo, the group in front gs, the flags kb, what is kept beside,
    the plain rows' type B and the rows' numbering, the joint beside, two default witnesses, the
    seats, the names, the callers' list, the drawn reader, a default sample, the fresh mask's word,
    the term for pS, the numbering no) WITH `K10Heavy` at the constant's letters, at p := b.place,
    and Q.k = gs.k.
  `k10_seated_of_heavy`: it gives `h.K10Seated L`. `k10_kind_of_heavy`: with the reading law:
    `h.Kind L .K10`.
Limits. BOOK-KEEPING AND CALLS: `K10Heavy`'s seventeen stand at every link; nothing is shown of any
state: the condition in front may be empty. Nothing on soundness.

-/
import Johnson.P5J.K10AsksFill
import Johnson.P5J.K10LawSeated

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item blockPlaces)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks K10Heavy groupLayK
  SlotNames SbV slV ZV pullOf placeFull closeFrame entries rdK wrK k10_smpNamed)
open OnBytes.Params Johnson.Pack Johnson.G Johnson.Top.H Cb Cb.Pv Iop IOR KObj
open OnBytes.Tie.Pv.Fold VerifiableInference.OnPublicFiles.BatFoldAt
open LPFK10 (ixK10)
open VerifiableInference.Desc.First.Close (kbAt kLay)
open VerifiableInference.Desc.ReqLit (shapeFull)

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

/-- The place of the sub-protocol number i is number i of the written list. -/
theorem k10_place_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i : ℕ) (b : Block TS ProofFile.Cl)
    (hi : cF.blocksInOrder[i]? = some b) : At.ps[i]? = some b.place := by
  rw [← At.places_paid h.scope h.reads h.laid]
  unfold blockPlaces
  rw [List.getElem?_map, hi]
  rfl

/-- **WHAT IS LEFT OF K10's OWN DEBT, WHOLE.** -/
def AtMgA.K10HeavyAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop :=
  ∀ (l : ℕ), l < 25 → ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (g0 : OnBytes.Params.GroupSize),
    g0 ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp l = some pw →
    ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 l]? = some b →
    (h.toAtMg.row L)[ixK10 l]? =
      some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) →
    b.place.kind = KindName.K10 → Q.k = g0.k →
    g0.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) →
    (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) →
    ∃ (lo : List (OracleShape × ℕ)) (gs : GroupSize) (kb : Fin lo.length → Bool) (hM : ∀ i, memMain
      lo i → (lo.get i).1.mainRows ≠ 0 → cMain (At.cs Zp) (lo.get i).1 = (stageOf gs 219).C) (hZ : ∀
      i, memMain lo i → (lo.get i).1.maskRows ≠ 0 → cMask (At.cs Zp) (lo.get i).1 = (stageOf gs
      219).Z) (keep : (sigOf (At.cs Zp) lo).O → Prop) (_ : DecidablePred keep) (B : Type) (_ :
      Fintype B) (num : (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).G.Row B ≃ Fin
      Q.rows) (Kc St₀ Wp : Type) (E₀ : ExtSpec) (A₀ : Rels Kc St₀ E₀ (((sigOf (At.cs Zp) lo).sub
      ((groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV (groupLayK (At.cs
      Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num)).kp).Msg × Wp)) (w₀ :
      (sigOf (At.cs Zp) lo).Wit × Wp) (w₁ : LdBrW (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ).G ((groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).sizeB keep (SbV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num)).kp
      Wp) (seat : Fin lo.length → ℕ × ℕ) (Nm : SlotNames (groupLayK (At.cs Zp) lo (stageOf gs 219)
      radFull kb hM hZ)) (Lc : List (BatFoldCaller GE)) (smpD : ProofFile.InstPub × TS → (i : Fin
            lo.length) → Option ((sigOf (At.cs Zp) lo).om i).Smp) (σ₀ : (sigOf (At.cs Zp) lo).Smp) (st₀ :
            St₀) (e₀ : E₀.Str) (mW : TS × (Frame.E FR).Str → (groupLayK (At.cs Zp) lo (stageOf gs 219)
            radFull kb hM hZ).Sh.par.Cw.nat.Str) (pS : ∀ as : (Σ a : (groupLayK (At.cs Zp) lo (stageOf gs
            219) radFull kb hM hZ).G.A, ((sigOf (At.cs Zp) lo).om a.1).Z.S), ((sigOf (At.cs Zp) lo).om
            as.1.1).Z.D → (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).Sh.Cin.J → GE) (no :
            Fin lo.length → ℕ),
      K10Heavy (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF) seat
        Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
        OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l)
        (VerifiableInference.Desc.First.Close.realRd ((groupLayK (At.cs Zp) lo (stageOf gs 219)
        radFull kb hM hZ).foldCaller keep (SbV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb
        hM hZ) B) (slV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) (pullOf
        (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo
        (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 : Fin 3), (1 : GE)) A₀ (placeFull
        gs.k).bC (placeFull gs.k).bZ w₀ w₁) (dBat Q.rows) dEps dTwo
        (VerifiableInference.Desc.First.Close.oneOf id) (VerifiableInference.Desc.First.Close.oneOf
        id)) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) b.place (XK h l) (oAt (ixK10 l)) no
        (h.toAtMg.row L) Q.k ∧ Q.k = gs.k

/-- **IT GIVES K10's DEBT.** -/
theorem k10_seated_of_heavy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10HeavyAll L) :
    h.K10Seated L := by
  intro l hl pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb
  obtain ⟨lo, gs, kb, hM, hZ, keep, iK, B, iB, num, Kc, St₀, Wp, E₀, A₀, w₀, w₁, seat, Nm, Lc, smpD,
    σ₀, st₀, e₀, mW, pS, no, A, hQ⟩ :=
    W l hl pw b Q g0 hg0 base h9 hQp hfl hS hBK e1 e2 Hb
  exact k10_piece_of_heavy h L q1 q2 q3 l b.place (k10_place_at h _ b hfl) hBK b Q base hS Hb lo gs
    kb hM hZ keep num A₀ w₀ w₁ seat Nm Lc smpD σ₀ st₀ e₀ mW pS no A hQ

/-- **THE FIELD OF THE KIND K10.** -/
theorem k10_kind_of_heavy (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (reads : ∀ (i : ℕ) (a : VerifiableInference.Desc.Place), At.ps[i]? = some a →
      a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (W : h.K10HeavyAll L) : h.Kind L .K10 :=
  k10_kind_at_seated h L q1 q2 q3 reads (k10_seated_of_heavy h L q1 q2 q3 W)

end P5J

#print axioms P5J.k10_place_at
#print axioms P5J.k10_seated_of_heavy
#print axioms P5J.k10_kind_of_heavy
