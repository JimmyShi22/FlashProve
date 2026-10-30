-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10LawSeated.lean: K10's OWN DEBT law AT THE CLOSED CONSTANT, DOWN TO ONE SENTENCE A
LINK ON THE PIECE THAT THE SEATED ROW HOLDS: THE SECOND FORM OF `AtMgA.K10Pieces`
(K10LawPieces.lean, beside this file), WHICH ASKS TOO MUCH. Statements and proofs: calls.

Why. `AtMgA.K10Pieces` speaks of every base and every Q with Q.k = gs.k: nothing ties them to the
seated row. But two premises of the assembled law hold at the row's own data alone: "every kept
tenant's tree lies below base" (`k10_T2_at`, K10KeptTests.lean: at the seated piece's own base; at
base 0 it is false wherever something is kept), and "the batching round's number of rows is the sum
of the three counts" (at the plan's own Q). So the first form cannot be paid along this road.
`k10_law_of_pieces` spends it only at what `k10_row_at` hands over.
  `AtMgA.K10Seated h L`: THE DEBT: as `K10Pieces`, WITH THREE MORE HYPOTHESES, all from
    `k10_row_at`: the link's place in the plan pw (`k9At Zp l = some pw`); Q IS THE PLAN's
    (`ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q`); THE SEATED ROW HOLDS THE PIECE at `ixK10 l`.
    It asks less than `K10Pieces` (`k10_seated_of_pieces`).
  `k10_law_of_seated`: it gives the field law, to the letter. `k10_two_of_seated`,
    `k10_kind_at_seated`: with reads: `h.K10Two L`; `h.Kind L .K10`.
Limits. BOOK-KEEPING: the debt is the field's own content, at the named pieces. Nothing on
soundness.

-/
import Johnson.P5J.K10LawPieces

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
open VerifiableInference.Desc.First (ModelPart Numbers start blockPlaces)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.Close (Par dBat dEps dTwo kbAt kLay closeFrame entries rdK wrK)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit)
open LPFK10 (ixK10 k10_row_at)

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

/-- **K10's OWN DEBT, A LINK A SENTENCE, ON THE PIECE THAT THE SEATED ROW HOLDS.** -/
def AtMgA.K10Seated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop :=
  ∀ (l : ℕ), l < 25 → ∀ (pw : VerifiableInference.Desc.K9.Where) (b : Block TS ProofFile.Cl) (Q : Par)
    (gs : OnBytes.Params.GroupSize),
    gs ∈ Johnson.G.frontFull → ∀ base : ℕ, IM.k9At Zp l = some pw →
    ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) pw = some Q → cF.blocksInOrder[ixK10 l]? = some b →
    (h.toAtMg.row L)[ixK10 l]? =
      some (pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo))) →
    b.place.kind = KindName.K10 → Q.k = gs.k →
    gs.k = kLay (linksFullLit.getD l []) (kbAt shapeFull l (linksFullLit.getD l [])) →
    (∀ s rs gs' s', b.decide s rs gs' = .ok s' → ∃ y, closeFrame (rdK s).1 (rdK s).2.1
      (rdK s).2.2 (entries Q) rs = .ok y ∧ s' = wrK s y.1 y.2) →
    ∃ o : ST → Prop,
      ((pieceOf (held b) base (dBat Q.rows :: dEps :: List.replicate Q.k dTwo) []
        (restCap L.e₁ (ixK10 l) (dBat Q.rows :: dEps :: List.replicate Q.k dTwo)) : PC).withMap
        (h.toAtMg.ex L (ixK10 l))).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (insQ fullLinks At.ps (ixK10 l)))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps (ixK10 l))) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) (ixK10 l) s →
        h.toAtMg.rch (ixK10 l) s → ¬ s.1.2.failed ≠ none → o s

/-- **IT GIVES THE FIELD law, TO THE LETTER.** -/
theorem k10_law_of_seated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Seated L) :
    ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∃ o : ST → Prop, (q.withMap (h.toAtMg.ex L i)).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a) (insQ fullLinks At.ps i))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps i)) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
        h.toAtMg.rch i s → ¬ s.1.2.failed ≠ none → o s := by
  intro i q a hq ha hk
  obtain ⟨B, -, -, hB, hBp, -, -, -⟩ := k10_block_at h i a ha hk
  have hBK : B.place.kind = KindName.K10 := by rw [hBp]; exact hk
  obtain ⟨l, hl, pw, Q, gs, hgs, base, h9, hQ, hfl, hrow, e1, e2, H⟩ :=
    k10_row_at h.toAtMg L q1 q2 q3 h.toAtMg.shape_full B (List.mem_of_getElem? hB) hBK
  obtain rfl : i = ixK10 l := k10_ix_of h i (ixK10 l) B hB hfl
  obtain rfl := Option.some.inj (hq.symm.trans hrow)
  exact W l hl pw B Q gs hgs base h9 hQ hfl hrow hBK e1 e2 H

/-- With reads: the two fields. -/
theorem k10_two_of_seated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (W : h.K10Seated L) : h.K10Two L :=
  ⟨reads, k10_law_of_seated h L q1 q2 q3 W⟩

/-- **THE FIELD OF THE KIND K10.** -/
theorem k10_kind_at_seated (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (W : h.K10Seated L) : h.Kind L .K10 :=
  k10_kind_at_two h L q1 q2 q3 (k10_two_of_seated h L q1 q2 q3 reads W)

/-- The second form asks less. -/
theorem k10_seated_of_pieces (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (W : h.K10Pieces L) :
    h.K10Seated L :=
  fun l hl _ b Q gs hgs base _ _ hfl _ hBK e1 e2 H => W l hl b Q gs hgs base hfl hBK e1 e2 H

end P5J

#print axioms P5J.k10_law_of_seated
#print axioms P5J.k10_two_of_seated
#print axioms P5J.k10_kind_at_seated
#print axioms P5J.k10_seated_of_pieces
