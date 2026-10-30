-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Two.lean: K10's DEBT AT THE CLOSED CONSTANT, AT THE CONCRETE SECOND HASH FUNCTION:
TWO FIELDS. A definition, statements and proofs: calls; no more.
Over Johnson/P5J/K10Own.lean.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `k10_room_at`: there is a free0 with `P1L20.RoomOwes cF (ProofFile.startS Zp) free0`: `K10Own`'s field
    room: by `roomOwes_paid` (Johnson/P1L20R/RoomKeepAll.lean) at the head's own
    scope, reading of the files and opening.
  `AtMgA.K10Two h L`: `K10Own`'s fields reads and law, to the letter. `k10_own_of_two`: it gives
    `h.K10Own L`. `k10_kind_at_two`: so, under the three flat lists' heads, `h.Kind L .K10`.
Limits. BOOK-KEEPING. `K10Two` IS THE DEBT: no member is known. reads is no kind's: a rider reads of
the witness only what the table says. law IS K10's OWN: it names a part of the conclusion
(`GoodIn`), with the first tie beside it, at one condition in front: it holds K10's whole knowledge
soundness. AT OnBytes.secondHashFunction ALONE. Nothing on soundness.

-/
import Johnson.P5J.K10Own
import Johnson.P1L20R.RoomKeepAll

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
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc (Chain KindName)

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

/-- **The debt `P1L20.RoomOwes` on the index masks' message is paid at the head.** -/
theorem k10_room_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ free0 : ℕ, P1L20.RoomOwes cF (ProofFile.startS Zp) free0 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨_, P1L20.roomOwes_paid h.scope h.reads O⟩

/-- **K10's DEBT: TWO FIELDS.** -/
structure AtMgA.K10Two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  /-- a rider reads of the witness only what the table says: no kind's -/
  reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
      h.toAtMg.rch i
  /-- the piece's law at the pick, and the first tie, at one condition in front -/
  law : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∃ o : ST → Prop, (q.withMap (h.toAtMg.ex L i)).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a) (insQ fullLinks At.ps i))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps i)) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
        h.toAtMg.rch i s → ¬ s.1.2.failed ≠ none → o s

/-- **The two give the three.** -/
theorem k10_own_of_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (W : h.K10Two L) : h.K10Own L :=
  ⟨W.reads, k10_room_at h, W.law⟩

/-- **THE FIELD, FROM THE TWO.** -/
theorem k10_kind_at_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Two L) :
    h.Kind L .K10 :=
  k10_kind_at_own h L q1 q2 q3 (k10_own_of_two h L W)

end P5J

#print axioms P5J.k10_room_at
#print axioms P5J.k10_own_of_two
#print axioms P5J.k10_kind_at_two
