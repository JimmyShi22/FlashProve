-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10LawPieces.lean: K10's OWN DEBT law (`AtMgA.K10Two`, K10Two.lean, beside this file) AT
THE CLOSED CONSTANT, DOWN TO ONE SENTENCE A LINK ON THE MAKER's OWN PIECE. Statements and proofs:
calls.

Why. The field law speaks of whatever piece q stands in the seated row at a number i whose place is
of the kind K10. `k10_row_at` (Johnson/LPFK10R/RowAtK10.lean) says which piece that
is: at link l, number `ixK10 l`: `pieceOf (held b) base (dBat Q.rows :: dEps :: Q.k times dTwo) []
(restCap L.e₁ ..)`. The assembled law (`k10_two_cs`, Johnson/Desc/First/Close/Law/LawTwoCs.lean)
speaks of a piece of just that form.
  `k10_ix_of`: a number i whose sub-protocol is the one at `ixK10 l` IS `ixK10 l`: the places are
    the written list (`At.places_paid`), in which no place stands twice (`flatPlaces_nodup`).
  `AtMgA.K10Pieces h L`: THE DEBT: at every link l below 25, every b, Q, gs, base with what
    `k10_row_at` says of them: there is a condition o with the law of THAT piece (the pick laid in)
    between the table's two relations at `ixK10 l`, and the first tie to o.
  `k10_law_of_pieces`: it gives the field law, to the letter. `k10_two_of_pieces`: with reads it
    gives `h.K10Two L`; `k10_kind_at_pieces`: so `h.Kind L .K10`.
Limits. BOOK-KEEPING: the debt is the field's own content, at named pieces. "The request's shape is
the written one" is `AtMg.shape_full`. Nothing on soundness.

-/
import Johnson.P5J.K10Two
import Johnson.P5J.ShapeFullAtMg
import Johnson.LPFK10R.RowAtK10

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

/-- A number whose sub-protocol is the one at another number is that number. -/
theorem k10_ix_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i j : ℕ) (b : Block TS ProofFile.Cl)
    (hi : cF.blocksInOrder[i]? = some b) (hj : cF.blocksInOrder[j]? = some b) : i = j := by
  have hpl := At.places_paid h.scope h.reads h.laid
  have e1 : At.ps[i]? = some b.place := by
    rw [← hpl]
    unfold blockPlaces
    rw [List.getElem?_map, hi]
    rfl
  have e2 : At.ps[j]? = some b.place := by
    rw [← hpl]
    unfold blockPlaces
    rw [List.getElem?_map, hj]
    rfl
  exact List.getElem?_inj (List.getElem?_eq_some_iff.1 e1).1
    (ProofFile.Law.flatPlaces_nodup fullLinks true) (e1.trans e2.symm)

/-- **K10's OWN DEBT, A LINK A SENTENCE, ON THE MAKER's OWN PIECE.** -/
def AtMgA.K10Pieces (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop :=
  ∀ (l : ℕ), l < 25 → ∀ (b : Block TS ProofFile.Cl) (Q : Par) (gs : OnBytes.Params.GroupSize),
    gs ∈ Johnson.G.frontFull → ∀ base : ℕ, cF.blocksInOrder[ixK10 l]? = some b →
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
theorem k10_law_of_pieces (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Pieces L) :
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
  obtain ⟨l, hl, -, Q, gs, hgs, base, -, -, hfl, hrow, e1, e2, H⟩ :=
    k10_row_at h.toAtMg L q1 q2 q3 h.toAtMg.shape_full B (List.mem_of_getElem? hB) hBK
  obtain rfl : i = ixK10 l := k10_ix_of h i (ixK10 l) B hB hfl
  obtain rfl := Option.some.inj (hq.symm.trans hrow)
  exact W l hl B Q gs hgs base hfl hBK e1 e2 H

/-- With reads: the two fields. -/
theorem k10_two_of_pieces (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (W : h.K10Pieces L) : h.K10Two L :=
  ⟨reads, k10_law_of_pieces h L q1 q2 q3 W⟩

/-- **THE FIELD OF THE KIND K10.** -/
theorem k10_kind_at_pieces (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
      ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
        h.toAtMg.rch i) (W : h.K10Pieces L) : h.Kind L .K10 :=
  k10_kind_at_two h L q1 q2 q3 (k10_two_of_pieces h L q1 q2 q3 reads W)

end P5J

#print axioms P5J.k10_ix_of
#print axioms P5J.k10_law_of_pieces
#print axioms P5J.k10_two_of_pieces
#print axioms P5J.k10_kind_at_pieces
