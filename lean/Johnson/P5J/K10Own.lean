-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K10Own.lean: K10's DEBT AT THE CLOSED CONSTANT, AT THE CONCRETE SECOND HASH FUNCTION,
WITH THREE MORE OF ITS SIX FIELDS STRUCK BY CALLS OF OTHER FILES' THEOREMS AT THE ONE HEAD. A
definition, statements and proofs: calls; no more.
Over Johnson/P5J/K10Debt.lean and K10Fence.lean.

What is said, at h : AtMgA OnBytes.secondHashFunction ..:
  `AtMgA.K10Own h L`: THREE FIELDS: `K10Debt`'s reads and law, to the letter; and room: there is a
    free0 with `P1L20.RoomOwes cF (ProofFile.startS Zp) free0`.
  `k10_debt_of_own`: it gives `h.K10Debt L`: fenFit by `AtMg.fence` (Johnson/P5T/FenceAtMg.lean);
    kept by `k10_kept_at` (Johnson/LPFE1R/K10KeptAt.lean); clear by `AtMg.clear`
    (Johnson/LPFE1R/K10ClearAt.lean); fence by `k10_fence_at` (Johnson/P5J/K10Fence.lean) from room.
    `k10_kind_at_own`: so, under the three flat lists' heads, `h.Kind L .K10`.
Limits. BOOK-KEEPING. `K10Own` IS THE DEBT: no member is known. law still names a part of the
conclusion (`GoodIn`), with the first tie beside it: it holds K10's whole knowledge soundness. reads
is no kind's. AT OnBytes.secondHashFunction ALONE. Nothing on soundness.

-/
import Johnson.P5J.K10Fence
import Johnson.P5T.FenceAtMg
import Johnson.LPFE1R.K10KeptAt
import Johnson.LPFE1R.K10ClearAt

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

/-- **K10's DEBT: THREE FIELDS.** -/
structure AtMgA.K10Own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  /-- a rider reads of the witness only what the table says: no kind's -/
  reads : ∀ (i : ℕ) (a : Place), At.ps[i]? = some a → a.kind = KindName.K10 →
    ReadsOkAtQR (Fr := FR) (At.arr Zp) (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a)
      h.toAtMg.rch i
  /-- the debt `P1L20.RoomOwes` on the index masks' message along the fold -/
  room : ∃ free0 : ℕ, P1L20.RoomOwes cF (ProofFile.startS Zp) free0
  /-- the piece's law at the pick, and the first tie, at one condition in front -/
  law : ∀ (i : ℕ) (q : PC) (a : Place), (h.toAtMg.row L)[i]? = some q → At.ps[i]? = some a →
    a.kind = KindName.K10 →
    ∃ o : ST → Prop, (q.withMap (h.toAtMg.ex L i)).GoodIn o (fun _ => True)
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a) (insQ fullLinks At.ps i))
        (relAt (meansQ (Fr := FR) (At.N Zp cF) (mgAtAll h) fun a => a)
          (outsQ fullLinks At.ps i)) ∧
      ∀ s : ST, onQ (At.N Zp cF) (mgAtAll h) fullLinks At.ps (fun a => a) i s →
        h.toAtMg.rch i s → ¬ s.1.2.failed ≠ none → o s

/-- **The three give the six.** -/
theorem k10_debt_of_own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) (W : h.K10Own L) :
    h.K10Debt L := by
  obtain ⟨free0, H⟩ := W.room
  exact ⟨W.reads, h.toAtMg.clear, h.toAtMg.fence, k10_kept_at h.toAtMg, k10_fence_at h H, W.law⟩

/-- **THE FIELD, FROM THE THREE.** -/
theorem k10_kind_at_own (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q1 : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q2 : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q3 : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃) (W : h.K10Own L) :
    h.Kind L .K10 :=
  k10_kind_at_debt h L q1 q2 q3 (k10_debt_of_own h L W)

end P5J

#print axioms P5J.k10_debt_of_own
#print axioms P5J.k10_kind_at_own
