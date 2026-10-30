-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10PieceOfAsks.lean: AT THE CLOSED CONSTANT: WHAT K10's ASSEMBLED LAW ASKS
(`K10TwoAsks`, Johnson/Desc/First/Close/Law/K10TwoAsks.lean), AT THE CONSTANT's OWN LETTERS, GIVES
THE SENTENCE OF K10's DEBT AT ONE LINK (`AtMgA.K10Pieces`, K10LawPieces.lean, beside this file). A
definition, a statement and its proof: calls.

Why. This is the joint between the law in letters and the head. It shows that the constant's own
types meet the law's letters: the codes `At.cs Zp`, the seated term, `At.arr Zp`, `At.smp Zp`,
`At.ms Zp Z.lay`, the constant's decoder, `At.tokOf`, `At.N Zp cF`, `mgAtAll h`, `fullLinks`,
`At.ps`, the first chain's frame, the maker's extractor.
  `XK h l`: the table's promise, "reached" and "no mark" at K10's border of link l: the law's letter
    X.
  `k10_piece_of_asks`: for a sub-protocol b, parameters Q and a base: `K10TwoAsks` at these letters
    (n := Q.rows, Pr := Q, ex := the maker's, k := ix := `ixK10 l`, X := `XK h l`) and Q.k = gs.k:
    THEN there is a condition o with: the law of `pieceOf (held b) base (dBat Q.rows :: dEps :: Q.k
    times dTwo) [] (restCap ..)`, the pick `h.toAtMg.ex` laid in, between the table's two relations
    at `ixK10 l`; and the first tie to o. By `k10_two_of_asks` and `AtMg.ex_is` (K10Letters.lean).
The typed letters (the list lo, the group in front gs, the flags kb, the numbering of the rows, the
names, the term for pS, the drawn reader, the fresh mask's word and the rest) stay letters: whoever
lays them in chooses them a link.
Limits. BOOK-KEEPING: no premise is discharged. Nothing on soundness.

-/
import Johnson.P5J.K10LawPieces
import Johnson.P5J.K10Letters
import Johnson.Desc.First.Close.Law.K10TwoAsks

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
open VerifiableInference.Desc.First (ModelPart Numbers start Item)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo K10TwoAsks k10_two_of_asks groupLayK
  SlotNames SbV slV ZV pullOf placeFull)
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

/-- The table's promise, "reached" and "no mark" at K10's border of link l. -/
def XK (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (s : ST) : Prop :=
  onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) s ∧
    h.toAtMg.rch (ixK10 l) s ∧ ¬ s.1.2.failed ≠ none

/-- **THE JOINT BETWEEN THE LAW IN LETTERS AND THE HEAD, AT ONE LINK.** -/
theorem k10_piece_of_asks (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (l : ℕ) (b : Block TS ProofFile.Cl)
    (Q : Par) (base : ℕ)
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
    (ρ : Rd ((groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ).foldCaller keep (SbV
      (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) B) (slV (groupLayK (At.cs Zp) lo
      (stageOf gs 219) radFull kb hM hZ) (pullOf (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull
      kb hM hZ))) (ZV (groupLayK (At.cs Zp) lo (stageOf gs 219) radFull kb hM hZ) Q.rows num) ((1 :
      Fin 3), (1 : GE)) A₀ (placeFull gs.k).bC (placeFull gs.k).bZ w₀ w₁) (wT (dBat Q.rows)) (wT
      dEps) (wT dTwo))
    (p : VerifiableInference.Desc.Place)
    (O : List Item)
    (no : Fin lo.length → ℕ)
    (row : List (Piece (ckP .two) FR (ProofFile.InstPub × TS) ProofFile.Cl (Wit (CellsM numsFull) At.Tok MsgT)))
    (k' : ℕ)
    (A : K10TwoAsks (At.cs Zp) lo gs kb hM hZ keep Q.rows num A₀ w₀ w₁ (F0T OnBytes.secondHashFunction Zp Np cF)
      seat Nm Lc (At.smp Zp) smpD σ₀ st₀ e₀ mW (At.arr Zp) (At.ms Zp Z.lay) (dtK (At.EAt Z)
      OnBytes.secondHashFunction Zp Np cF h.toAtMg.plan.shape 0) L.c₀ At.tokOf pS Q b base L.e₁ (ixK10 l) ρ
      (At.N Zp cF) (mgAtAll h) fullLinks At.ps (ixK10 l) p (XK h l) O no row k')
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
        h.toAtMg.rch (ixK10 l) s → ¬ s.1.2.failed ≠ none → o s := by
  obtain ⟨q, hq, o, hG, ho⟩ := k10_two_of_asks _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A
  obtain rfl : k' = Q.k := A.hk'.trans hQ.symm
  obtain rfl := Option.some.inj (hq.symm.trans A.hrw)
  rw [AtMg.ex_is]
  exact ⟨o, hG, fun s h1 h2 h3 => ho s ⟨h1, h2, h3⟩⟩

end P5J

#print axioms P5J.k10_piece_of_asks
